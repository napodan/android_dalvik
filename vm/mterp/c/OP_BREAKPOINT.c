HANDLE_OPCODE(OP_BREAKPOINT)
#if (INTERP_TYPE == INTERP_DBG)
    {
        /*
         * Restart this instruction with the original opcode.  We do
         * this by simply jumping to the handler.
         *
         * It's probably not necessary to update "inst", but we do it
         * for the sake of anything that needs to do disambiguation in a
         * common handler with INST_INST.
         *
         * The breakpoint itself is handled over in updateDebugger(),
         * because we need to detect other events (method entry, single
         * step) and report them in the same event packet, and we're not
         * yet handling those through breakpoint instructions.  By the
         * time we get here, the breakpoint has already been handled and
         * the thread resumed.
         */
        u1 originalOpcode = dvmGetOriginalOpcode(pc);
        ALOGV("+++ break 0x%02x (0x%04x -> 0x%04x)\n", originalOpcode, inst,
            INST_REPLACE_OP(inst, originalOpcode));
        inst = INST_REPLACE_OP(inst, originalOpcode);
        FINISH_BKPT(originalOpcode);
    }
#else
    ALOGE("Breakpoint hit in non-debug interpreter\n");
    dvmAbort();
#endif
OP_END
