/*
 * Copyright (C) 2010 The Android Open Source Project
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

#ifndef _DALVIK_ALLOC_VISIT
#define _DALVIK_ALLOC_VISIT
#ifdef __cplusplus
extern "C" {
#endif


#include "Dalvik.h"

typedef enum {
  ROOT_UNKNOWN = 0,
  ROOT_JNI_GLOBAL,
  ROOT_JNI_LOCAL,
  ROOT_JAVA_FRAME,
  ROOT_NATIVE_STACK,
  ROOT_STICKY_CLASS,
  ROOT_THREAD_BLOCK,
  ROOT_MONITOR_USED,
  ROOT_THREAD_OBJECT,
  ROOT_INTERNED_STRING,
  ROOT_FINALIZING,
  ROOT_DEBUGGER,
  ROOT_REFERENCE_CLEANUP,
  ROOT_VM_INTERNAL,
  ROOT_JNI_MONITOR,
} RootType;

/*
 * Callback invoked with the address of a reference and a user
 * supplied context argument.
 */
typedef void Visitor(void *addr, void *arg);

/*
 * Like a Visitor, but passes root specific information such as the
 * containing thread id and the root type.  In cases where a root is
 * not specific to a thread, 0, an invalid thread id is provided.
 */
typedef void RootVisitor(void *addr, u4 threadId, RootType type, void *arg);

/*
 * Visits references in an object.
 */
void dvmVisitObject(Visitor *visitor, Object *obj, void *arg);

/*
 * Visits references in the root set.
 */
void dvmVisitRoots(RootVisitor *visitor, void *arg);

#ifdef __cplusplus
};
#endif


#endif /* _DALVIK_ALLOC_VISIT */
