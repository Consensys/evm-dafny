include "../../dafny/util/bytes.dfy"
include "utils.dfy"

module ByteTests{
    import opened Bytes
    import opened Utils

    method {:test} ReadTests() {
        // U8
        Assert(() => ReadUint8([],0) == 0);
        Assert(() => ReadUint8([0],0) == 0);
        Assert(() => ReadUint8([1],0) == 1);
        Assert(() => ReadUint8([1],1) == 0);
        Assert(() => ReadUint8([1,2],0) == 1);
        Assert(() => ReadUint8([1,2],1) == 2);
        // U16
        Assert(() => ReadUint16([],0) == 0);
        Assert(() => ReadUint16([0],0) == 0);
        Assert(() => ReadUint16([0],1) == 0);
        Assert(() => ReadUint16([0,0],0) == 0);
        Assert(() => ReadUint16([0,1],0) == 1);
        Assert(() => ReadUint16([1,0],0) == 256);
        Assert(() => ReadUint16([0xFF],0) == 0xFF00);
        Assert(() => ReadUint16([0xFF,0],0) == 0xFF00);
        Assert(() => ReadUint16([0xFF,1],0) == 0xFF01);
        // U32
        Assert(() => ReadUint32([],0) == 0);
        Assert(() => ReadUint32([0],0) == 0);
        Assert(() => ReadUint32([0xFF],0) == 0xFF00_0000);
        Assert(() => ReadUint32([0,0xFF],0) == 0x00FF_0000);
        Assert(() => ReadUint32([0,0xFF,0],0) == 0x00FF_0000);
        Assert(() => ReadUint32([0,0xFF,0,0xD],0) == 0x00FF_000D);
        Assert(() => ReadUint32([0,0xFF,0,0xD],1) == 0xFF_000D00);
        // U64
        Assert(() => ReadUint64([],0) == 0);
        Assert(() => ReadUint64([0],0) == 0);
        Assert(() => ReadUint64([0xFF],0) == 0xFF00_0000_0000_0000);
        Assert(() => ReadUint64([0,0xFF],0) == 0x00FF_0000_0000_0000);
        Assert(() => ReadUint64([0,0xFF,0],0) == 0x00FF_0000_0000_0000);
        Assert(() => ReadUint64([0,0xFF,0,0xD],0) == 0x00FF_000D_0000_0000);
        Assert(() => ReadUint64([0,0xFF,0,0xD],1) == 0xFF_000D00_0000_0000);
        Assert(() => ReadUint64([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF_000D_0A0B_0000);
        Assert(() => ReadUint64([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF_000D0A_0B00_0000);
        Assert(() => ReadUint64([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B);
        // U128
        Assert(() => ReadUint128([],0) == 0);
        Assert(() => ReadUint128([0],0) == 0);
        Assert(() => ReadUint128([0xFF],0) == 0xFF000000_00000000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF],0) == 0x00FF0000_00000000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF,0],0) == 0x00FF0000_00000000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF,0,0xD],0) == 0x00FF000D_00000000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF,0,0xD],1) == 0xFF000D00_00000000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF000D_0A0B0000_00000000_00000000);
        Assert(() => ReadUint128([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF_000D0A_0B00_0000_00000000_00000000);
        Assert(() => ReadUint128([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B_00000000_00000000);
        Assert(() => ReadUint128([0xFF,0xA,0xB,0xC,0xD,0xE,0xF,0x1A,0x1B, 0x1C,0x1D,0x1E,0x1F,0x2A,0x2B,0x2C,0x2D],1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D);
        // U256
        Assert(() => ReadUint256([],0) == 0);
        Assert(() => ReadUint256([0],0) == 0);
        Assert(() => ReadUint256([],0) == 0);
        Assert(() => ReadUint256([0],0) == 0);
        Assert(() => ReadUint256([0xFF],0) == 0xFF00000000000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF],0) == 0x00FF000000000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF,0],0) == 0x00FF000000000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF,0,0xD],0) == 0x00FF000D00000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF,0,0xD],1) == 0xFF000D0000000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF,0,0xD,0xA,0xB],0) == 0x00FF000D0A0B0000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0,0xFF,0,0xD,0xA,0xB],1) == 0xFF000D0A0B000000_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0xFF,0xA,0xB,0xC,0xD, 0xE,0xF,0x1A,0x1B],1) == 0x0A0B0C0D0E0F1A1B_0000000000000000_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0xFF,0xA,0xB,0xC,0xD,0xE,0xF,0x1A,0x1B, 0x1C,0x1D,0x1E,0x1F,0x2A,0x2B,0x2C,0x2D],1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D_0000000000000000_0000000000000000);
        Assert(() => ReadUint256([0xFF,0xA,0xB,0xC,0xD,0xE,0xF,0x1A,0x1B, 0x1C,0x1D,0x1E,0x1F,0x2A,0x2B,0x2C,0x2D, 0x2E,0x2F,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,  0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,0x5A,0x5B],1) == 0x0A0B0C0D0E0F1A1B_1C1D1E1F2A2B2C2D_2E2F3A3B3C3D3E3F_4A4B4C4D4E4F5A5B);
    }

    method {:test} SliceTests() {
        Assert(() => Slice([0],0,0) == []);
        Assert(() => Slice([0],0,1) == [0]);
        Assert(() => Slice([1],0,1) == [1]);
        Assert(() => Slice([1,2],0,1) == [1]);
        Assert(() => Slice([1,2],1,1) == [2]);
        Assert(() => Slice([1,2],1,2) == [2,0]);
        Assert(() => Slice([1,2,3],1,2) == [2,3]);
    }

    method {:test} LeftPadTests() {
        Assert(() => LeftPad([0],2) == [0,0]);
        Assert(() => LeftPad([1],2) == [0,1]);
        Assert(() => LeftPad([1],4) == [0,0,0,1]);
        Assert(() => LeftPad([1,2],4) == [0,0,1,2]);
    }
}