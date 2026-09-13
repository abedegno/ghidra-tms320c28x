// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Nishanth Samala
// Reunite functions that seeding cut in two.
//
// THE PROBLEM. SeedFunctions signal B seeds on a PROLOGUE run -- consecutive callee-saved pushes
// (`MOVL *SP++,XARn`, `MOV32 *SP++,RnH`). That signature is genuine, but it is not exclusive to a
// function's first instruction: a compiler emits the same pushes MID-function when it needs another
// callee-saved register partway through a body, and TI's does so constantly. At seed time nothing
// can tell the two apart -- no code has been decoded, so there is no "previous instruction" to ask.
// The seed lands inside a live function and splits it. The half with the prologue keeps the name and
// the callers; the half with the epilogue keeps the LRETR and inherits NOTHING, because a
// fall-through is not a reference. It then reads as dead code, and so does everything only it calls.
//
// Measured on an F28377D CPU2 image: 107 such splits stranded 377 of 826 unreachable functions --
// including a 1371-word body and the component framework's own registry-walk loop, whose 69
// recovered dispatch edges were all hanging off an entry nothing could reach.
//
// THE SIGNAL, and why it is safe. Compiled code enters a function by CALLING it. So an entry that
// (a) nothing references, by call, jump or data, and (b) whose address appears nowhere in the image
// as a 32-bit value -- no table can hold a pointer to it -- and (c) sits exactly on the fall-through
// of the instruction before it, is not an entry at all. It is the middle of the function before it.
// Requirement (d) makes it conclusive: that preceding function contains NO return instruction
// anywhere in its body, so it cannot be a complete function -- its epilogue is on the other side of
// the cut. All four held on 105 of 107 sites on the image above and 89 of 89 on a CPU1 image; the
// exceptions are refused, not repaired.
//
// This runs LATE, after disassembly and function bodies have settled (post-FinalizeRamfuncs), for
// the same reason the seeder cannot do it: the evidence is the decoded fall-through.
//
// A user-renamed function is never merged away -- only DEFAULT-named (FUN_/SUB_) splits are, so a
// name you applied to the far half survives, and re-running after one changes nothing. Every merge
// leaves an Analysis bookmark at the seam.
//
// PHANTOM REFERENCES, removed first. SeedFunctions' raw call scan adds a call xref wherever two words
// encode LCR/LC/FFC -- including the operand word of a real instruction and a pair of table cells.
// Nothing executes from there, and now that the listing is decoded that is checkable: a flow
// reference whose source is not the start of an instruction is deleted. Each one was propping up a
// function, usually the far half of a split that (a) would otherwise have merged. A target left with
// no references that still cannot merge (data, a hand-named function, a stored address) gets an
// Analysis / c28x-phantom-orphan bookmark saying why; SweepResidualMarks lists those for review.
// Only USER_DEFINED flow references are touched -- the source SeedFunctions writes.
//
// Properties (-Dname=value):
//   c28x.split.dryRun        (bool, default false) report only; make no changes
//   c28x.split.rounds        (int,  default 4)     fixpoint cap (a split can chain into another)
//   c28x.split.allowOwnerRet (bool, default false) drop requirement (d) -- looser, less certain
//   c28x.split.keepPhantomRefs(bool, default false) skip the phantom-reference pass
//
// @category TMS320C28x
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceManager;
import ghidra.program.model.symbol.SourceType;
import java.util.ArrayList;
import java.util.HashSet;

public class MergeSplitFunctions extends GhidraScript {

    // run_ghidra_script / the MCP bridge deliver -Dkey=value as getScriptArgs(), not as JVM system
    // properties. Clear first: properties are JVM-global and survive between runs in one session.
    void promoteDashDArgs() {
        for (String k : new ArrayList<>(System.getProperties().stringPropertyNames()))
            if (k.startsWith("c28x.split.")) System.clearProperty(k);
        String[] args = getScriptArgs();
        if (args == null) return;
        for (String a : args) {
            if (a == null || !a.startsWith("-D")) continue;
            String kv = a.substring(2);
            int eq = kv.indexOf('=');
            if (eq > 0) System.setProperty(kv.substring(0, eq), kv.substring(eq + 1));
            else if (!kv.isEmpty()) System.setProperty(kv, "true");
        }
    }

    long w(Address a) { return a.getOffset() / 2; }

    /** Every 32-bit little-endian value present in initialized memory, at any word alignment. */
    HashSet<Long> imageValues() {
        HashSet<Long> vals = new HashSet<>();
        for (MemoryBlock b : currentProgram.getMemory().getBlocks()) {
            if (!b.isInitialized()) continue;
            Address a = b.getStart();
            long lo = w(a), hi = w(b.getEnd());
            for (long x = lo; x + 1 <= hi; x++) {
                try {
                    vals.add((currentProgram.getMemory().getShort(a.getNewAddress(x * 2)) & 0xFFFFL)
                        | ((currentProgram.getMemory().getShort(a.getNewAddress(x * 2 + 2))
                            & 0xFFFFL) << 16));
                } catch (Exception e) { /* unreadable word: nothing to record */ }
            }
        }
        return vals;
    }

    boolean hasReturn(Function f) {
        for (Instruction i : currentProgram.getListing().getInstructions(f.getBody(), true))
            if (i.getFlowType().isTerminal()) return true;
        return false;
    }

    boolean defaultNamed(Function f) {
        String n = f.getName();
        return n.startsWith("FUN_") || n.startsWith("SUB_") || n.startsWith("thunk_FUN_");
    }

    /** A flow xref from somewhere that is not an instruction start: nothing can execute from there. */
    boolean isPhantom(Reference r) {
        return r.getReferenceType().isFlow() && r.getSource() == SourceType.USER_DEFINED
            && currentProgram.getListing().getInstructionAt(r.getFromAddress()) == null;
    }

    boolean ignorePhantoms = true;

    /** References to `a` that are not phantoms. In a dry run the phantoms are still present. */
    int realRefCount(Address a) {
        int n = 0;
        for (Reference r : currentProgram.getReferenceManager().getReferencesTo(a))
            if (!ignorePhantoms || !isPhantom(r)) n++;
        return n;
    }

    @Override
    public void run() throws Exception {
        promoteDashDArgs();
        boolean dry = Boolean.getBoolean("c28x.split.dryRun");
        boolean allowRet = Boolean.getBoolean("c28x.split.allowOwnerRet");
        int rounds = Integer.getInteger("c28x.split.rounds", 4);
        var fm = currentProgram.getFunctionManager();
        ReferenceManager rm = currentProgram.getReferenceManager();

        HashSet<Long> vals = imageValues();
        println("32-bit values present in the image: " + vals.size());

        // Pass 0: phantom flow references. Collect first -- deleting while iterating the DB is unsafe.
        java.util.TreeSet<Address> phantomTargets = new java.util.TreeSet<>();
        java.util.TreeMap<Address, Address> phantomFrom = new java.util.TreeMap<>();
        ignorePhantoms = !Boolean.getBoolean("c28x.split.keepPhantomRefs");
        if (ignorePhantoms) {
            ArrayList<Reference> phantoms = new ArrayList<>();
            for (Address from : rm.getReferenceSourceIterator(currentProgram.getMemory(), true))
                for (Reference r : rm.getReferencesFrom(from))
                    if (isPhantom(r)) phantoms.add(r);
            for (Reference r : phantoms) {
                phantomTargets.add(r.getToAddress());
                phantomFrom.putIfAbsent(r.getToAddress(), r.getFromAddress());
                if (!dry) rm.delete(r);
            }
            println((dry ? "would delete " : "deleted ") + phantoms.size() + " phantom flow reference(s) to "
                + phantomTargets.size() + " target(s)");
        }

        int merged = 0, refused = 0;
        HashSet<Long> refusedAt = new HashSet<>(), mergedAt = new HashSet<>();
        for (int round = 1; round <= rounds; round++) {
            ArrayList<Function> cands = new ArrayList<>();
            for (Function f : fm.getFunctions(true)) cands.add(f);
            int inRound = 0;
            for (Function f : cands) {
                if (monitor.isCancelled()) break;
                Address entry = f.getEntryPoint();
                if (fm.getFunctionAt(entry) == null) continue;      // merged away earlier this round
                if (!defaultNamed(f)) continue;
                if (realRefCount(entry) > 0) continue;              // (a) something points at it
                if (vals.contains(w(entry))) continue;              // (b) a table could hold it

                Instruction prev = getInstructionBefore(entry);
                if (prev == null) continue;
                Address ft = prev.getFallThrough();
                if (ft == null || !ft.equals(entry)) continue;      // (c) not entered by fall-through

                Function owner = fm.getFunctionContaining(prev.getAddress());
                if (owner == null || owner.getEntryPoint().equals(entry)) continue;
                if (owner.getBody().intersects(f.getBody())) continue;
                if (!allowRet && hasReturn(owner)) {                // (d) owner looks complete
                    if (refusedAt.add(w(entry))) {
                        refused++;
                        println(String.format("  refused %05x <- %05x %s: the owner already returns"
                            + " somewhere, so it may be a whole function", w(entry),
                            w(owner.getEntryPoint()), owner.getName()));
                    }
                    continue;
                }

                println(String.format("%s %05x (%d words) into %05x %s", dry ? "would merge" : "merge",
                    w(entry), f.getBody().getNumAddresses() / 2, w(owner.getEntryPoint()),
                    owner.getName()));
                mergedAt.add(w(entry));
                if (dry) { merged++; inRound++; continue; }

                AddressSetView body = new AddressSet(owner.getBody()).union(f.getBody());
                fm.removeFunction(entry);
                try {
                    owner.setBody(body);
                } catch (Exception e) {
                    // put the split back rather than leaving the half orphaned with no function
                    println("  FAILED to extend " + owner.getName() + ": " + e.getMessage()
                        + " -- restoring " + String.format("%05x", w(entry)));
                    new ghidra.app.cmd.function.CreateFunctionCmd(entry)
                        .applyTo(currentProgram, monitor);
                    continue;
                }
                if (owner.hasNoReturn() && hasReturn(owner)) owner.setNoReturn(false);
                currentProgram.getBookmarkManager().setBookmark(entry, "Analysis",
                    "c28x-merged-split", "seeded mid-function; merged back into "
                        + owner.getName());
                merged++;
                inRound++;
            }
            println("round " + round + ": " + inRound + " merge(s)");
            if (inRound == 0 || dry) break;
        }

        // Phantom targets now referenced by nothing that the rounds above could not merge.
        int orphans = 0;
        for (Address t : phantomTargets) {
            Function f = fm.getFunctionAt(t);
            if (f == null || mergedAt.contains(w(t)) || realRefCount(t) > 0) continue;
            Instruction prev = getInstructionBefore(t);
            boolean onFallThrough = prev != null && t.equals(prev.getFallThrough());
            Function owner = prev == null ? null : fm.getFunctionContaining(prev.getAddress());
            String why = !defaultNamed(f)
                    ? "named by hand" + (onFallThrough ? "; on the fall-through of " + prev.getAddress()
                        + ", so the real entry may be earlier" : "")
                : vals.contains(w(t)) ? "its address is stored in the image as a 32-bit value"
                : !onFallThrough ? "not on a fall-through: data decoded as code, or an entry nothing references"
                : owner == null ? "the instruction before it is in no function"
                : "the function before it already returns";
            orphans++;
            println(String.format("  orphan %05x %s (%d words): %s", w(t), f.getName(),
                f.getBody().getNumAddresses() / 2, why));
            if (!dry) currentProgram.getBookmarkManager().setBookmark(t, "Analysis", "c28x-phantom-orphan",
                "only reference was a phantom call from " + phantomFrom.get(t) + "; not merged: " + why);
        }

        println("");
        println(merged + " split function(s) " + (dry ? "would be merged" : "merged")
            + ", " + refused + " refused, " + orphans + " phantom orphan(s)"
            + (dry || orphans == 0 ? "" : " bookmarked (Analysis / c28x-phantom-orphan)"));
        if (merged > 0 && !dry)
            println("re-run ReachabilityReport: everything those halves called is now reachable"
                + " through the function that actually contains them.");
    }
}
