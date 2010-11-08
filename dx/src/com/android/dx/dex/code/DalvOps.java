/*
 * Copyright (C) 2007 The Android Open Source Project
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

package com.android.dx.dex.code;

/**
 * All the Dalvik opcode value constants. See the related spec
 * document for the meaning and instruction format of each opcode.
 */
public final class DalvOps {
    /** pseudo-opcode used for nonstandard format "instructions" */
    public static final int SPECIAL_FORMAT = -1;

    /** pseudo-opcode used to indicate there is no next opcode */
    public static final int NO_NEXT = -1;

    /** minimum valid opcode value */
    public static final int MIN_VALUE = -1;

    /** maximum valid opcode value */
    public static final int MAX_VALUE = 0xff;

    // BEGIN(opcodes); GENERATED AUTOMATICALLY BY opcode-gen
    public static final int NOP = 0x00;
    public static final int MOVE = 0x01;
    public static final int MOVE_FROM16 = 0x02;
    public static final int MOVE_16 = 0x03;
    public static final int MOVE_WIDE = 0x04;
    public static final int MOVE_WIDE_FROM16 = 0x05;
    public static final int MOVE_WIDE_16 = 0x06;
    public static final int MOVE_OBJECT = 0x07;
    public static final int MOVE_OBJECT_FROM16 = 0x08;
    public static final int MOVE_OBJECT_16 = 0x09;
    public static final int MOVE_RESULT = 0x0a;
    public static final int MOVE_RESULT_WIDE = 0x0b;
    public static final int MOVE_RESULT_OBJECT = 0x0c;
    public static final int MOVE_EXCEPTION = 0x0d;
    public static final int RETURN_VOID = 0x0e;
    public static final int RETURN = 0x0f;
    public static final int RETURN_WIDE = 0x10;
    public static final int RETURN_OBJECT = 0x11;
    public static final int CONST_4 = 0x12;
    public static final int CONST_16 = 0x13;
    public static final int CONST = 0x14;
    public static final int CONST_HIGH16 = 0x15;
    public static final int CONST_WIDE_16 = 0x16;
    public static final int CONST_WIDE_32 = 0x17;
    public static final int CONST_WIDE = 0x18;
    public static final int CONST_WIDE_HIGH16 = 0x19;
    public static final int CONST_STRING = 0x1a;
    public static final int CONST_STRING_JUMBO = 0x1b;
    public static final int CONST_CLASS = 0x1c;
    public static final int MONITOR_ENTER = 0x1d;
    public static final int MONITOR_EXIT = 0x1e;
    public static final int CHECK_CAST = 0x1f;
    public static final int INSTANCE_OF = 0x20;
    public static final int ARRAY_LENGTH = 0x21;
    public static final int NEW_INSTANCE = 0x22;
    public static final int NEW_ARRAY = 0x23;
    public static final int FILLED_NEW_ARRAY = 0x24;
    public static final int FILLED_NEW_ARRAY_RANGE = 0x25;
    public static final int FILL_ARRAY_DATA = 0x26;
    public static final int THROW = 0x27;
    public static final int GOTO = 0x28;
    public static final int GOTO_16 = 0x29;
    public static final int GOTO_32 = 0x2a;
    public static final int PACKED_SWITCH = 0x2b;
    public static final int SPARSE_SWITCH = 0x2c;
    public static final int CMPL_FLOAT = 0x2d;
    public static final int CMPG_FLOAT = 0x2e;
    public static final int CMPL_DOUBLE = 0x2f;
    public static final int CMPG_DOUBLE = 0x30;
    public static final int CMP_LONG = 0x31;
    public static final int IF_EQ = 0x32;
    public static final int IF_NE = 0x33;
    public static final int IF_LT = 0x34;
    public static final int IF_GE = 0x35;
    public static final int IF_GT = 0x36;
    public static final int IF_LE = 0x37;
    public static final int IF_EQZ = 0x38;
    public static final int IF_NEZ = 0x39;
    public static final int IF_LTZ = 0x3a;
    public static final int IF_GEZ = 0x3b;
    public static final int IF_GTZ = 0x3c;
    public static final int IF_LEZ = 0x3d;
    public static final int UNUSED_3E = 0x3e;
    public static final int UNUSED_3F = 0x3f;
    public static final int UNUSED_40 = 0x40;
    public static final int UNUSED_41 = 0x41;
    public static final int UNUSED_42 = 0x42;
    public static final int UNUSED_43 = 0x43;
    public static final int AGET = 0x44;
    public static final int AGET_WIDE = 0x45;
    public static final int AGET_OBJECT = 0x46;
    public static final int AGET_BOOLEAN = 0x47;
    public static final int AGET_BYTE = 0x48;
    public static final int AGET_CHAR = 0x49;
    public static final int AGET_SHORT = 0x4a;
    public static final int APUT = 0x4b;
    public static final int APUT_WIDE = 0x4c;
    public static final int APUT_OBJECT = 0x4d;
    public static final int APUT_BOOLEAN = 0x4e;
    public static final int APUT_BYTE = 0x4f;
    public static final int APUT_CHAR = 0x50;
    public static final int APUT_SHORT = 0x51;
    public static final int IGET = 0x52;
    public static final int IGET_WIDE = 0x53;
    public static final int IGET_OBJECT = 0x54;
    public static final int IGET_BOOLEAN = 0x55;
    public static final int IGET_BYTE = 0x56;
    public static final int IGET_CHAR = 0x57;
    public static final int IGET_SHORT = 0x58;
    public static final int IPUT = 0x59;
    public static final int IPUT_WIDE = 0x5a;
    public static final int IPUT_OBJECT = 0x5b;
    public static final int IPUT_BOOLEAN = 0x5c;
    public static final int IPUT_BYTE = 0x5d;
    public static final int IPUT_CHAR = 0x5e;
    public static final int IPUT_SHORT = 0x5f;
    public static final int SGET = 0x60;
    public static final int SGET_WIDE = 0x61;
    public static final int SGET_OBJECT = 0x62;
    public static final int SGET_BOOLEAN = 0x63;
    public static final int SGET_BYTE = 0x64;
    public static final int SGET_CHAR = 0x65;
    public static final int SGET_SHORT = 0x66;
    public static final int SPUT = 0x67;
    public static final int SPUT_WIDE = 0x68;
    public static final int SPUT_OBJECT = 0x69;
    public static final int SPUT_BOOLEAN = 0x6a;
    public static final int SPUT_BYTE = 0x6b;
    public static final int SPUT_CHAR = 0x6c;
    public static final int SPUT_SHORT = 0x6d;
    public static final int INVOKE_VIRTUAL = 0x6e;
    public static final int INVOKE_SUPER = 0x6f;
    public static final int INVOKE_DIRECT = 0x70;
    public static final int INVOKE_STATIC = 0x71;
    public static final int INVOKE_INTERFACE = 0x72;
    public static final int UNUSED_73 = 0x73;
    public static final int INVOKE_VIRTUAL_RANGE = 0x74;
    public static final int INVOKE_SUPER_RANGE = 0x75;
    public static final int INVOKE_DIRECT_RANGE = 0x76;
    public static final int INVOKE_STATIC_RANGE = 0x77;
    public static final int INVOKE_INTERFACE_RANGE = 0x78;
    public static final int UNUSED_79 = 0x79;
    public static final int UNUSED_7A = 0x7a;
    public static final int NEG_INT = 0x7b;
    public static final int NOT_INT = 0x7c;
    public static final int NEG_LONG = 0x7d;
    public static final int NOT_LONG = 0x7e;
    public static final int NEG_FLOAT = 0x7f;
    public static final int NEG_DOUBLE = 0x80;
    public static final int INT_TO_LONG = 0x81;
    public static final int INT_TO_FLOAT = 0x82;
    public static final int INT_TO_DOUBLE = 0x83;
    public static final int LONG_TO_INT = 0x84;
    public static final int LONG_TO_FLOAT = 0x85;
    public static final int LONG_TO_DOUBLE = 0x86;
    public static final int FLOAT_TO_INT = 0x87;
    public static final int FLOAT_TO_LONG = 0x88;
    public static final int FLOAT_TO_DOUBLE = 0x89;
    public static final int DOUBLE_TO_INT = 0x8a;
    public static final int DOUBLE_TO_LONG = 0x8b;
    public static final int DOUBLE_TO_FLOAT = 0x8c;
    public static final int INT_TO_BYTE = 0x8d;
    public static final int INT_TO_CHAR = 0x8e;
    public static final int INT_TO_SHORT = 0x8f;
    public static final int ADD_INT = 0x90;
    public static final int SUB_INT = 0x91;
    public static final int MUL_INT = 0x92;
    public static final int DIV_INT = 0x93;
    public static final int REM_INT = 0x94;
    public static final int AND_INT = 0x95;
    public static final int OR_INT = 0x96;
    public static final int XOR_INT = 0x97;
    public static final int SHL_INT = 0x98;
    public static final int SHR_INT = 0x99;
    public static final int USHR_INT = 0x9a;
    public static final int ADD_LONG = 0x9b;
    public static final int SUB_LONG = 0x9c;
    public static final int MUL_LONG = 0x9d;
    public static final int DIV_LONG = 0x9e;
    public static final int REM_LONG = 0x9f;
    public static final int AND_LONG = 0xa0;
    public static final int OR_LONG = 0xa1;
    public static final int XOR_LONG = 0xa2;
    public static final int SHL_LONG = 0xa3;
    public static final int SHR_LONG = 0xa4;
    public static final int USHR_LONG = 0xa5;
    public static final int ADD_FLOAT = 0xa6;
    public static final int SUB_FLOAT = 0xa7;
    public static final int MUL_FLOAT = 0xa8;
    public static final int DIV_FLOAT = 0xa9;
    public static final int REM_FLOAT = 0xaa;
    public static final int ADD_DOUBLE = 0xab;
    public static final int SUB_DOUBLE = 0xac;
    public static final int MUL_DOUBLE = 0xad;
    public static final int DIV_DOUBLE = 0xae;
    public static final int REM_DOUBLE = 0xaf;
    public static final int ADD_INT_2ADDR = 0xb0;
    public static final int SUB_INT_2ADDR = 0xb1;
    public static final int MUL_INT_2ADDR = 0xb2;
    public static final int DIV_INT_2ADDR = 0xb3;
    public static final int REM_INT_2ADDR = 0xb4;
    public static final int AND_INT_2ADDR = 0xb5;
    public static final int OR_INT_2ADDR = 0xb6;
    public static final int XOR_INT_2ADDR = 0xb7;
    public static final int SHL_INT_2ADDR = 0xb8;
    public static final int SHR_INT_2ADDR = 0xb9;
    public static final int USHR_INT_2ADDR = 0xba;
    public static final int ADD_LONG_2ADDR = 0xbb;
    public static final int SUB_LONG_2ADDR = 0xbc;
    public static final int MUL_LONG_2ADDR = 0xbd;
    public static final int DIV_LONG_2ADDR = 0xbe;
    public static final int REM_LONG_2ADDR = 0xbf;
    public static final int AND_LONG_2ADDR = 0xc0;
    public static final int OR_LONG_2ADDR = 0xc1;
    public static final int XOR_LONG_2ADDR = 0xc2;
    public static final int SHL_LONG_2ADDR = 0xc3;
    public static final int SHR_LONG_2ADDR = 0xc4;
    public static final int USHR_LONG_2ADDR = 0xc5;
    public static final int ADD_FLOAT_2ADDR = 0xc6;
    public static final int SUB_FLOAT_2ADDR = 0xc7;
    public static final int MUL_FLOAT_2ADDR = 0xc8;
    public static final int DIV_FLOAT_2ADDR = 0xc9;
    public static final int REM_FLOAT_2ADDR = 0xca;
    public static final int ADD_DOUBLE_2ADDR = 0xcb;
    public static final int SUB_DOUBLE_2ADDR = 0xcc;
    public static final int MUL_DOUBLE_2ADDR = 0xcd;
    public static final int DIV_DOUBLE_2ADDR = 0xce;
    public static final int REM_DOUBLE_2ADDR = 0xcf;
    public static final int ADD_INT_LIT16 = 0xd0;
    public static final int RSUB_INT = 0xd1;
    public static final int MUL_INT_LIT16 = 0xd2;
    public static final int DIV_INT_LIT16 = 0xd3;
    public static final int REM_INT_LIT16 = 0xd4;
    public static final int AND_INT_LIT16 = 0xd5;
    public static final int OR_INT_LIT16 = 0xd6;
    public static final int XOR_INT_LIT16 = 0xd7;
    public static final int ADD_INT_LIT8 = 0xd8;
    public static final int RSUB_INT_LIT8 = 0xd9;
    public static final int MUL_INT_LIT8 = 0xda;
    public static final int DIV_INT_LIT8 = 0xdb;
    public static final int REM_INT_LIT8 = 0xdc;
    public static final int AND_INT_LIT8 = 0xdd;
    public static final int OR_INT_LIT8 = 0xde;
    public static final int XOR_INT_LIT8 = 0xdf;
    public static final int SHL_INT_LIT8 = 0xe0;
    public static final int SHR_INT_LIT8 = 0xe1;
    public static final int USHR_INT_LIT8 = 0xe2;
    public static final int UNUSED_E3 = 0xe3;
    public static final int UNUSED_E4 = 0xe4;
    public static final int UNUSED_E5 = 0xe5;
    public static final int UNUSED_E6 = 0xe6;
    public static final int UNUSED_E7 = 0xe7;
    public static final int UNUSED_E8 = 0xe8;
    public static final int UNUSED_E9 = 0xe9;
    public static final int UNUSED_EA = 0xea;
    public static final int UNUSED_EB = 0xeb;
    public static final int UNUSED_EC = 0xec;
    public static final int UNUSED_ED = 0xed;
    public static final int UNUSED_EE = 0xee;
    public static final int UNUSED_EF = 0xef;
    public static final int UNUSED_F0 = 0xf0;
    public static final int UNUSED_F1 = 0xf1;
    public static final int UNUSED_F2 = 0xf2;
    public static final int UNUSED_F3 = 0xf3;
    public static final int UNUSED_F4 = 0xf4;
    public static final int UNUSED_F5 = 0xf5;
    public static final int UNUSED_F6 = 0xf6;
    public static final int UNUSED_F7 = 0xf7;
    public static final int UNUSED_F8 = 0xf8;
    public static final int UNUSED_F9 = 0xf9;
    public static final int UNUSED_FA = 0xfa;
    public static final int UNUSED_FB = 0xfb;
    public static final int UNUSED_FC = 0xfc;
    public static final int UNUSED_FD = 0xfd;
    public static final int UNUSED_FE = 0xfe;
    public static final int UNUSED_FF = 0xff;
    // END(opcodes)

    /**
     * This class is uninstantiable.
     */
    private DalvOps() {
        // This space intentionally left blank.
    }

    /**
     * Determines if the given opcode has the right "shape" to be
     * valid. This includes the range {@code 0x00..0xfe}, the range
     * {@code 0x00ff..0xffff} where the low-order byte is {@code
     * 0xff}, and the special opcode values {@code SPECIAL_FORMAT} and
     * {@code NO_NEXT}. Note that not all of the opcode values that
     * pass this test are in fact used. This method is meant to
     * perform a quick check to reject blatantly wrong values (e.g.
     * when validating arguments).
     *
     * @param opcode the opcode value
     * @return {@code true} iff the value has the right "shape" to be
     * possibly valid
     */
    public static boolean isValidShape(int opcode) {
        // Note: SPECIAL_FORMAT == NO_NEXT.
        if ((opcode >= SPECIAL_FORMAT) && (opcode <= 0xff)) {
            return true;
        }

        if ((opcode >= 0xff) && (opcode <= 0xffff)
                && ((opcode & 0xff) == 0xff)) {
            return true;
        }

        return false;
    }
}
