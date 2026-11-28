import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.function.IntPredicate;

import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.ValuesReader;
import org.apache.parquet.column.values.ValuesWriter;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesReaderForDouble;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesReaderForFLBA;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesReaderForFloat;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesReaderForInteger;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesReaderForLong;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesWriter.DoubleByteStreamSplitValuesWriter;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesWriter.FixedLenByteArrayByteStreamSplitValuesWriter;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesWriter.FloatByteStreamSplitValuesWriter;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesWriter.IntegerByteStreamSplitValuesWriter;
import org.apache.parquet.column.values.bytestreamsplit.ByteStreamSplitValuesWriter.LongByteStreamSplitValuesWriter;
import org.apache.parquet.io.api.Binary;

/** Emits parquet-java 1.16.0 lanes after a typed reader round trip. */
public class ByteStreamSplitOracle {
    private static void emit(String name, int width, int count, ValuesWriter writer,
                             ValuesReader reader, IntPredicate agrees) throws IOException {
        if (writer.getEncoding() != Encoding.BYTE_STREAM_SPLIT) {
            throw new AssertionError(writer.getEncoding());
        }
        var output = new ByteArrayOutputStream();
        writer.getBytes().writeAllTo(output);
        byte[] lanes = output.toByteArray();
        if (lanes.length != width * count) throw new AssertionError(name + " extent");
        reader.initFromPage(count, ByteBufferInputStream.wrap(ByteBuffer.wrap(lanes)));
        for (int index = 0; index < count; ++index) {
            if (!agrees.test(index)) throw new AssertionError(name + " readback " + index);
        }
        System.out.printf("%s\t%d\t%d\t%s%n", name, count, width, HexFormat.of().formatHex(lanes));
    }

    public static void main(String[] args) throws IOException {
        var allocator = HeapByteBufferAllocator.getInstance();
        int[] ints = {Integer.MIN_VALUE, -2, 0x01020304, Integer.MAX_VALUE};
        try (var writer = new IntegerByteStreamSplitValuesWriter(64, 1024, allocator)) {
            for (int value : ints) writer.writeInteger(value);
            var reader = new ByteStreamSplitValuesReaderForInteger();
            emit("INT32", 4, ints.length, writer, reader, i -> reader.readInteger() == ints[i]);
        }
        long[] longs = {Long.MIN_VALUE, -2, 0x0102030405060708L, Long.MAX_VALUE};
        try (var writer = new LongByteStreamSplitValuesWriter(64, 1024, allocator)) {
            for (long value : longs) writer.writeLong(value);
            var reader = new ByteStreamSplitValuesReaderForLong();
            emit("INT64", 8, longs.length, writer, reader, i -> reader.readLong() == longs[i]);
        }
        int[] floats = {0x80000000, 0x3fa00000, 0xff800000, 0x7fc00000};
        try (var writer = new FloatByteStreamSplitValuesWriter(64, 1024, allocator)) {
            for (int bits : floats) writer.writeFloat(Float.intBitsToFloat(bits));
            var reader = new ByteStreamSplitValuesReaderForFloat();
            emit("FLOAT", 4, floats.length, writer, reader,
                    i -> Float.floatToRawIntBits(reader.readFloat()) == floats[i]);
        }
        long[] doubles = {0x8000000000000000L, 0x3ff4000000000000L, 0xfff0000000000000L, 0x7ff8000000000000L};
        try (var writer = new DoubleByteStreamSplitValuesWriter(64, 1024, allocator)) {
            for (long bits : doubles) writer.writeDouble(Double.longBitsToDouble(bits));
            var reader = new ByteStreamSplitValuesReaderForDouble();
            emit("DOUBLE", 8, doubles.length, writer, reader,
                    i -> Double.doubleToRawLongBits(reader.readDouble()) == doubles[i]);
        }
        byte[][] fixed = {{0, (byte) 0xff, 0x41}, {(byte) 0x80, 0, 0x7f}, {0x11, 0x22, 0x33}};
        try (var writer = new FixedLenByteArrayByteStreamSplitValuesWriter(3, 64, 1024, allocator)) {
            for (byte[] value : fixed) writer.writeBytes(Binary.fromConstantByteArray(value));
            var reader = new ByteStreamSplitValuesReaderForFLBA(3);
            emit("FIXED_LEN_BYTE_ARRAY", 3, fixed.length, writer, reader,
                    i -> Arrays.equals(reader.readBytes().getBytes(), fixed[i]));
        }
    }
}
