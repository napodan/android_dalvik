/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Mterp entry point and support functions.
 */
#include "Dalvik.h"
#include "mterp/Mterp.h"

#include <stddef.h>


/*
 * Verify some constants used by the mterp interpreter.
 */
bool dvmCheckAsmConstants()
{
    bool failed = false;

#ifndef DVM_NO_ASM_INTERP

    extern char dvmAsmInstructionStart[];
    extern char dvmAsmInstructionEnd[];

#define ASM_DEF_VERIFY
#include "mterp/common/asm-constants.h"

    if (failed) {
        ALOGE("Please correct the values in mterp/common/asm-constants.h");
        dvmAbort();
    }

    /*
     * If we're using computed goto instruction transitions, make sure
     * none of the handlers overflows the 64-byte limit.  This won't tell
     * which one did, but if any one is too big the total size will
     * overflow.
     */
#if defined(__mips__)
    const int width = 128;
#else
    const int width = 64;
#endif
    int interpSize = (uintptr_t) dvmAsmInstructionEnd -
                     (uintptr_t) dvmAsmInstructionStart;
    if (interpSize != 0 && interpSize != kNumPackedOpcodes*width) {
        ALOGE("ERROR: unexpected asm interp size %d", interpSize);
        ALOGE("(did an instruction handler exceed %d bytes?)", width);
        dvmAbort();
    }

#endif // ndef DVM_NO_ASM_INTERP

    return !failed;
}


/*
 * "Mterp entry point.
 */
bool dvmMterpStd(Thread* self, InterpState* glue)
{
    int changeInterp;

    /* configure mterp items */
    glue->self = self;
    glue->methodClassDex = glue->method->clazz->pDvmDex;

    glue->interpStackEnd = self->interpStackEnd;
    glue->pSelfSuspendCount = &self->suspendCount;
    glue->cardTable = gDvm.biasedCardTableBase;
#if defined(WITH_JIT)
    glue->pJitProfTable = gDvmJit.pProfTable;
    glue->ppJitProfTable = &gDvmJit.pProfTable;
    glue->jitThreshold = gDvmJit.threshold;
#endif
    if (gDvm.jdwpConfigured) {
        glue->pDebuggerActive = &gDvm.debuggerActive;
    } else {
        glue->pDebuggerActive = NULL;
    }
    glue->pActiveProfilers = &gDvm.activeProfilers;

    IF_LOGVV() {
        char* desc = dexProtoCopyMethodDescriptor(
                         &glue->method->prototype);
        LOGVV("mterp threadid=%d entry %d: %s.%s %s",
            dvmThreadSelf()->threadId,
            glue->entryPoint,
            glue->method->clazz->descriptor,
            glue->method->name,
            desc);
        free(desc);
    }
    //ALOGI("self is %p, pc=%p, fp=%p", self, self->interpSave.pc,
    //      self->interpSave.curFrame);
    //ALOGI("first instruction is 0x%04x", self->interpSave.pc[0]);

    changeInterp = dvmMterpStdRun(glue);

#if defined(WITH_JIT)
    if (glue->jitState != kJitSingleStep) {
        glue->self->inJitCodeCache = NULL;
    }
#endif

    if (!changeInterp) {
        /* this is a "normal" exit; we're not coming back */
#ifdef LOG_INSTR
    ALOGD("|-- Leaving interpreter loop");
#endif
        return false;
    } else {
        /* we're "standard", so switch to "debug" */
        LOGVV("  mterp returned, changeInterp=%d\n", changeInterp);
        glue->nextMode = INTERP_DBG;
        return true;
    }
}