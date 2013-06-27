HANDLE_OPCODE(OP_INVOKE_DIRECT_EMPTY /*vB, {vD, vE, vF, vG, vA}, meth@CCCC*/)
#if INTERP_TYPE != INTERP_DBG
    //ALOGI("Ignoring empty\n");
    FINISH(3);
#else
    if (!gDvm.debuggerActive) {
        //ALOGI("Skipping empty\n");
        FINISH(3);      // don't want it to show up in profiler output
    } else {
        //ALOGI("Running empty\n");
        /* fall through to OP_INVOKE_DIRECT */
        GOTO_invoke(invokeDirect, false);
    }
#endif
OP_END
