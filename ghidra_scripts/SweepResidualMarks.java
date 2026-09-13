// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Nishanth Samala
//
// Step 7 of the image-setup pipeline (docs/C28X_IMAGE_SETUP.md): go through the bookmarks the
// pipeline leaves behind, clear the ones that are settled, and gather everything that looks like a
// wrong decode into one review list.
//
//   Error marks        classified (below); only the provably cosmetic class is deleted.
//   c28x-merged-split  MergeSplitFunctions' seam notes. The merge is done, so they are deleted.
//   c28x-phantom-orphan  a function whose only reference MergeSplitFunctions deleted as a phantom
//                      and could not merge. Listed for review; deleted once the function is gone or
//                      has a real reference. Never deletes the function itself.
//   Found Code         Ghidra's operand-reference analyzer decoded code at an address only a data
//                      reference names. Each becomes a function -- unless its decode fails a
//                      sanity check, in which case it goes on the review list instead.
//
// The bulk of post-pipeline Error marks are phantom decodes: the disassembler speculatively
// decoded a const pool, a flash load image, or inter-function padding before
// MarkDataTables/MaterializeSections claimed those bytes as data. Once the byte is a
// data (or undefined) code unit, the mark on it describes an instruction that no longer
// exists. Those are safe to drop wholesale.
//
// What is NOT dropped, because each can be a genuine finding:
//   - a mark on a real instruction inside a function  -> possible missing opcode
//   - a mark on a loose instruction outside any function -> code/data boundary or a
//     committed-state artifact; wants a human look
//   - a "flow into uninitialized memory" mark -> an un-materialized section (back to step 4/4b)
//   - a flow to an address no block maps -> the instruction's operands are wrong: a wrong decode,
//     or data decoded as code
//
// DECODE REVIEW. The in-function marks, loose marks, flows to unmapped addresses and suspect Found
// Code are printed together, each with its words and decode, and bookmarked Warning /
// c28x-decode-suspect. Most turn out to be data decoded as code, which dis2000 decodes the same way;
// run tests/run_fw_parity over the site before calling one a spec bug.
//
// Default is a DRY RUN: it prints the classification and changes nothing. Pass "apply"
// as the script argument to delete, create functions and bookmark the review list.
//
//   run_ghidra_script SweepResidualMarks.java            # report only
//   run_ghidra_script SweepResidualMarks.java  apply     # act on it
//
//@category TMS320C28x
import ghidra.app.cmd.function.CreateFunctionCmd;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.Bookmark;
import ghidra.program.model.listing.BookmarkManager;
import ghidra.program.model.listing.BookmarkType;
import ghidra.program.model.listing.CodeUnit;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.FlowType;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SweepResidualMarks extends GhidraScript {

    /** "…memory at 00180048 (flow from …)" — the address the dangling flow targets. */
    private static final Pattern FLOW_TARGET =
            Pattern.compile("memory at ([0-9a-fA-F]+)");

    private static final String MERGED_SPLIT = "c28x-merged-split";
    private static final String FOUND_CODE = "Found Code";
    private static final String PHANTOM_ORPHAN = "c28x-phantom-orphan";
    private static final String SUSPECT = "c28x-decode-suspect";

    /** cl2000 does not emit these from C: TRAP #n is 0x0020|n, ITRAP0 0x0000, ITRAP1 0xffff. */
    private static final Set<String> TRAP_CLASS = Set.of("TRAP", "ITRAP0", "ITRAP1", "ABORTI");

    private record Suspect(Address addr, String why) {}

    @Override
    public void run() throws Exception {
        boolean apply = false;
        for (String a : getScriptArgs()) {
            if (a.equalsIgnoreCase("apply")) {
                apply = true;
            }
        }

        BookmarkManager bm = currentProgram.getBookmarkManager();

        List<Bookmark> cosmetic = new ArrayList<>();   // mark sits on data/undefined
        List<Bookmark> inFunction = new ArrayList<>(); // real instruction, in a function
        List<Bookmark> loose = new ArrayList<>();      // real instruction, no function
        List<Bookmark> deadFlow = new ArrayList<>();   // flow target still uninitialized
        List<Suspect> review = new ArrayList<>();

        Iterator<Bookmark> it = bm.getBookmarksIterator(BookmarkType.ERROR);
        while (it.hasNext()) {
            Bookmark b = it.next();
            Address addr = b.getAddress();
            String comment = b.getComment() == null ? "" : b.getComment();

            CodeUnit cu = currentProgram.getListing().getCodeUnitAt(addr);
            boolean isInsn = cu instanceof Instruction;
            Function fn = getFunctionContaining(addr);

            if (comment.contains("not permitted within uninitialized")) {
                // Names no address. The mark sits on the target itself, or on an instruction
                // whose flow reaches it; either way an EMIF target is a review item, not a gap.
                MemoryBlock ext = currentProgram.getMemory().getBlock(addr);
                if (ext == null || !isExternalMemory(ext)) {
                    ext = null;
                    if (cu instanceof Instruction insn) {
                        for (Address t : insn.getFlows()) {
                            MemoryBlock tb = currentProgram.getMemory().getBlock(t);
                            if (tb != null && isExternalMemory(tb)) {
                                ext = tb;
                            }
                        }
                    }
                }
                if (ext != null) {
                    review.add(new Suspect(addr, "flow into external memory " + ext.getName()
                            + (fn == null ? "" : ", in " + fn.getName()) + " -- " + comment));
                }
                else {
                    deadFlow.add(b);
                }
                continue;
            }
            Address target = flowTarget(comment);
            if (target != null) {
                MemoryBlock blk = currentProgram.getMemory().getBlock(target);
                if (blk == null) {
                    // No block maps the target, so the operands are garbage. Once the bytes are
                    // data, the instruction that carried them is gone and so is the finding.
                    if (!isInsn && fn == null) {
                        cosmetic.add(b);
                    }
                    else {
                        review.add(new Suspect(addr, "flow to " + target
                                + ", unmapped in this program" + (fn == null ? "" : ", in "
                                        + fn.getName()) + " -- " + comment));
                    }
                    continue;
                }
                if (isExternalMemory(blk)) {
                    // No image step fills external memory, so this is not a section awaiting
                    // materialization: either the board runs code there or the decode is wrong.
                    review.add(new Suspect(addr, "flow into external memory " + blk.getName()
                            + (fn == null ? "" : ", in " + fn.getName()) + " -- " + comment));
                    continue;
                }
                if (!blk.isInitialized()) {
                    deadFlow.add(b);
                    continue;
                }
                // The target holds bytes now, so the mark is stale: classify it like any other.
                // FinalizeRamfuncs pass 1b clears these, so reaching here is rare.
            }

            if (fn != null) {
                // Inside a function body. An address here that did NOT decode is the most
                // interesting case there is: SeedFunctions bound a function whose very
                // first word the disassembler could not resolve, which is the signature of
                // a missing opcode. Never treat that as cosmetic just because the failed
                // decode left an undefined code unit behind.
                inFunction.add(b);
                review.add(new Suspect(addr, "Error mark in " + fn.getName() + " -- " + comment));
            }
            else if (!isInsn) {
                cosmetic.add(b);          // data / undefined / nothing, outside any function
            }
            else {
                loose.add(b);
                review.add(new Suspect(addr, "Error mark on a loose instruction -- " + comment));
            }
        }

        List<Bookmark> merged = new ArrayList<>();
        List<Bookmark> orphanResolved = new ArrayList<>();
        List<Address> toCreate = new ArrayList<>();
        List<String> foundInside = new ArrayList<>();
        int found = 0, foundIsFn = 0;
        Iterator<Bookmark> ait = bm.getBookmarksIterator(BookmarkType.ANALYSIS);
        while (ait.hasNext()) {
            Bookmark b = ait.next();
            if (MERGED_SPLIT.equals(b.getCategory())) {
                merged.add(b);
                continue;
            }
            if (PHANTOM_ORPHAN.equals(b.getCategory())) {
                Address a = b.getAddress();
                Function f = getFunctionAt(a);
                if (f == null || getReferencesTo(a).length > 0) {
                    orphanResolved.add(b);   // deleted by hand, merged, or something real calls it now
                    continue;
                }
                String why = foundCodeSuspect(a, f);
                review.add(new Suspect(a, "phantom orphan " + f.getName() + ": " + b.getComment()
                        + (why == null ? "" : "; " + why)));
                continue;
            }
            if (!FOUND_CODE.equals(b.getCategory())) {
                continue;
            }
            found++;
            Address a = b.getAddress();
            Function owner = getFunctionContaining(a);
            if (owner != null && !owner.getEntryPoint().equals(a)) {
                // A data reference into the middle of a body is a constant that happens to equal
                // a code address, not an entry. Splitting the function would be wrong.
                foundInside.add(a + " inside " + owner.getName());
                continue;
            }
            String why = foundCodeSuspect(a, owner);
            if (why != null) {
                review.add(new Suspect(a, "Found Code: " + why));
            }
            else if (owner == null) {
                toCreate.add(a);
            }
            else {
                foundIsFn++;
            }
        }

        int created = 0;
        if (apply) {
            for (Bookmark b : cosmetic) {
                bm.removeBookmark(b);
            }
            for (Bookmark b : merged) {
                bm.removeBookmark(b);
            }
            for (Bookmark b : orphanResolved) {
                bm.removeBookmark(b);
            }
            for (Address a : toCreate) {
                if (createFunction(a, null) != null) {
                    created++;
                }
                else {
                    review.add(new Suspect(a, "Found Code: function creation failed"));
                }
            }
        }

        String verb = apply ? "deleted" : "deletable";
        println("=== residual Error marks: " + (cosmetic.size() + inFunction.size()
                + loose.size() + deadFlow.size()) + " ===");
        report("cosmetic (mark on data/undefined -- " + verb + ")", cosmetic);
        report("KEEP: on an instruction inside a function (possible missing opcode)", inFunction);
        report("KEEP: on a loose instruction (code/data boundary -- review)", loose);
        report("KEEP: flow into uninitialized memory (un-materialized section?)", deadFlow);
        println("");
        println("=== " + MERGED_SPLIT + ": " + merged.size() + " (" + verb + ") ===");
        println("=== " + PHANTOM_ORPHAN + ": resolved " + orphanResolved.size() + " (" + verb
                + "), still standing: listed under DECODE REVIEW ===");
        println("=== Found Code: " + found + " ===");
        println("  " + (apply ? "functions created: " + created : "would create: " + toCreate.size())
                + ", already a function: " + foundIsFn
                + ", suspect (not created): " + (found - toCreate.size() - foundIsFn
                        - foundInside.size())
                + ", inside another function (left alone): " + foundInside.size());
        for (String s : foundInside) {
            println("      " + s);
        }

        review.sort(Comparator.comparing(Suspect::addr));
        println("");
        println("=== DECODE REVIEW: " + review.size() + " ===");
        if (!review.isEmpty()) {
            println("  check each against dis2000 (tests/run_fw_parity) before calling it a spec bug");
        }
        for (Suspect s : review) {
            printSuspect(s);
        }

        if (!apply) {
            println("");
            println("DRY RUN -- nothing changed. Re-run with the 'apply' argument to delete "
                    + (cosmetic.size() + merged.size()) + " mark(s), create " + toCreate.size()
                    + " function(s) and bookmark the review list.");
            return;
        }

        // Replace the previous run's list, so a site that now decodes cleanly loses its bookmark.
        bm.removeBookmarks(BookmarkType.WARNING, SUSPECT, monitor);
        for (Suspect s : review) {
            bm.setBookmark(s.addr(), BookmarkType.WARNING, SUSPECT, s.why());
        }
        println("");
        println("applied: deleted " + cosmetic.size() + " cosmetic + " + merged.size()
                + " merged-split mark(s); created " + created + " function(s); bookmarked "
                + review.size() + " for review (Warning / " + SUSPECT + ").");
    }

    /** An EMIF chip-select window as SetupF28377D names it (EMIF1_CS2 …), not the EMIF register frame. */
    private static boolean isExternalMemory(MemoryBlock b) {
        return !b.isInitialized() && b.getName().matches("EMIF\\d_CS\\d");
    }

    /**
     * The address a "could not follow disassembly flow into …" mark names, or null. Parsed the way
     * Ghidra printed it: this space displays WORD offsets, while getAddress(long) takes bytes.
     */
    private Address flowTarget(String comment) {
        if (!comment.contains("follow disassembly flow")) {
            return null;
        }
        Matcher m = FLOW_TARGET.matcher(comment);
        return m.find() ? currentProgram.getAddressFactory().getAddress(m.group(1)) : null;
    }

    /**
     * Why the code at a Found Code mark does not look like a function entry, or null when it does.
     * Checks the existing body when there is a function, else the body one would get.
     */
    private String foundCodeSuspect(Address entry, Function fn) {
        Listing listing = currentProgram.getListing();
        if (listing.getInstructionAt(entry) == null) {
            Instruction host = listing.getInstructionContaining(entry);
            return host != null
                    ? "the mark is an operand word of " + host.getAddress() + " " + host
                    : "nothing decodes at the mark (" + listing.getCodeUnitAt(entry) + ")";
        }
        AddressSetView body = fn != null ? fn.getBody()
                : CreateFunctionCmd.getFunctionBody(currentProgram, entry);
        Set<String> why = new LinkedHashSet<>();
        String stack = freesBeforeAllocating(entry);
        if (stack != null) {
            why.add(stack);
        }
        // No NOP check: cl2000 FPU code in ramfuncs carries NOP runs that dis2000 confirms.
        boolean exits = false;
        for (Instruction i : listing.getInstructions(body, true)) {
            String mn = i.getMnemonicString().toUpperCase();
            if (TRAP_CLASS.contains(mn)) {
                why.add(mn + " at " + i.getAddress() + " (a small integer or 0xffff read as code)");
            }
            FlowType ft = i.getFlowType();
            if (ft.isTerminal() || (ft.isJump() && !ft.isConditional())) {
                exits = true;
            }
            for (Address t : i.getFlows()) {
                MemoryBlock tb = currentProgram.getMemory().getBlock(t);
                if (tb == null) {
                    why.add("flow to " + t + " at " + i.getAddress() + ", unmapped in this program");
                }
                else if (isExternalMemory(tb)) {
                    why.add("flow to " + t + " at " + i.getAddress() + ", external memory "
                            + tb.getName());
                }
            }
            Address fall = i.getFallThrough();
            if (fall != null && listing.getInstructionAt(fall) == null) {
                why.add("falls through into data at " + fall);
            }
            if (currentProgram.getBookmarkManager()
                    .getBookmarks(i.getAddress(), BookmarkType.ERROR).length > 0) {
                why.add("Error mark in the body at " + i.getAddress());
            }
        }
        if (!exits) {
            why.add("no return or unconditional branch in the body");
        }
        return why.isEmpty() ? null : String.join("; ", why);
    }

    /**
     * A cl2000 entry pushes or allocates before it pops or frees. Walking the fall-through from the
     * entry, a pop or SUBB SP first means the "entry" is somewhere in the middle of a function.
     */
    private String freesBeforeAllocating(Address entry) {
        Listing listing = currentProgram.getListing();
        Instruction i = listing.getInstructionAt(entry);
        for (int n = 0; i != null && n < 16; n++) {
            String t = i.toString().toUpperCase();
            if (t.contains("*SP++") || t.startsWith("ADDB SP")) {
                return null;
            }
            if (t.contains("*--SP") || t.startsWith("SUBB SP")) {
                return "frees stack at " + i.getAddress() + " (" + i
                        + ") before allocating any -- mid-function entry?";
            }
            Address fall = i.getFallThrough();
            i = fall == null ? null : listing.getInstructionAt(fall);
        }
        return null;
    }

    private void printSuspect(Suspect s) {
        println("  " + s.addr() + "  " + s.why());
        Listing listing = currentProgram.getListing();
        Instruction i = listing.getInstructionAt(s.addr());
        if (i == null) {
            i = listing.getInstructionContaining(s.addr());
        }
        for (int n = 0; n < 4 && i != null; n++) {
            println(String.format("      %s  %-15s %s", i.getAddress(), words(i), i));
            Address fall = i.getFallThrough();
            i = fall == null ? null : listing.getInstructionAt(fall);
        }
    }

    /** The instruction's words as dis2000 prints them (little-endian 16-bit parcels). */
    private static String words(Instruction i) {
        StringBuilder sb = new StringBuilder();
        try {
            byte[] b = i.getBytes();
            for (int k = 0; k + 1 < b.length; k += 2) {
                sb.append(String.format("%04x ", ((b[k + 1] & 0xff) << 8) | (b[k] & 0xff)));
            }
        }
        catch (Exception e) {
            sb.append("????");
        }
        return sb.toString().trim();
    }

    private void report(String label, List<Bookmark> list) {
        println("  " + label + ": " + list.size());
        int shown = 0;
        for (Bookmark b : list) {
            if (shown++ >= 12) {
                println("      … and " + (list.size() - 12) + " more");
                break;
            }
            Function f = getFunctionContaining(b.getAddress());
            println("      " + b.getAddress() + (f == null ? "" : "  in " + f.getName())
                    + "  -- " + b.getComment());
        }
    }
}
