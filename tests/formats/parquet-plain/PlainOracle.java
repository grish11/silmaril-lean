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
import org.apache.parquet.column.values.plain.BooleanPlainValuesReader;
import org.apache.parquet.column.values.plain.BooleanPlainValuesWriter;
import org.apache.parquet.column.values.plain.FixedLenByteArrayPlainValuesReader;
import org.apache.parquet.column.values.plain.FixedLenByteArrayPlainValuesWriter;
import org.apache.parquet.column.values.plain.PlainValuesReader.DoublePlainValuesReader;
import org.apache.parquet.column.values.plain.PlainValuesReader.FloatPlainValuesReader;
import org.apache.parquet.column.values.plain.PlainValuesReader.IntegerPlainValuesReader;
import org.apache.parquet.column.values.plain.PlainValuesReader.LongPlainValuesReader;
import org.apache.parquet.column.values.plain.PlainValuesWriter;
import org.apache.parquet.io.api.Binary;

/** Emits unframed PLAIN payloads from parquet-java 1.16.0 after checking its readers. */
public class PlainOracle {
    private static PlainValuesWriter writer() {
        return new PlainValuesWriter(64, 1024, HeapByteBufferAllocator.getInstance());
    }

    private static void emit(String name, ValuesWriter writer, ValuesReader reader,
                             int count, IntPredicate agrees) throws IOException {
        if (writer.getEncoding() != Encoding.PLAIN) {
            throw new AssertionError(name + " selected " + writer.getEncoding());
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        writer.getBytes().writeAllTo(output);
        byte[] bytes = output.toByteArray();
        reader.initFromPage(count, ByteBufferInputStream.wrap(ByteBuffer.wrap(bytes)));
        for (int i = 0; i < count; ++i) {
            if (!agrees.test(i)) {
                throw new AssertionError(name + " value " + i);
            }
        }
        System.out.printf("%s\t%d\t%s%n", name, count, HexFormat.of().formatHex(bytes));
    }

    public static void main(String[] args) throws IOException {
        int[] ints = {Integer.MIN_VALUE, -2, 0, 0x01020304, Integer.MAX_VALUE};
        try (PlainValuesWriter out = writer()) {
            for (int value : ints) out.writeInteger(value);
            var in = new IntegerPlainValuesReader();
            emit("INT32", out, in, ints.length, i -> in.readInteger() == ints[i]);
        }

        long[] longs = {Long.MIN_VALUE, -2, 0, 0x0102030405060708L, Long.MAX_VALUE};
        try (PlainValuesWriter out = writer()) {
            for (long value : longs) out.writeLong(value);
            var in = new LongPlainValuesReader();
            emit("INT64", out, in, longs.length, i -> in.readLong() == longs[i]);
        }

        boolean[] bits = {true, false, true, true, false, false, false, true, false, true, true};
        try (var out = new BooleanPlainValuesWriter()) {
            for (boolean value : bits) out.writeBoolean(value);
            var in = new BooleanPlainValuesReader();
            emit("BOOLEAN", out, in, bits.length, i -> in.readBoolean() == bits[i]);
        }

        byte[][] fixed = {{0, (byte) 255, 65}, {(byte) 128, 0, 127}};
        try (var out = new FixedLenByteArrayPlainValuesWriter(
                3, 64, 1024, HeapByteBufferAllocator.getInstance())) {
            for (byte[] value : fixed) out.writeBytes(Binary.fromConstantByteArray(value));
            var in = new FixedLenByteArrayPlainValuesReader(3);
            emit("FIXED_LEN_BYTE_ARRAY(3)", out, in, fixed.length,
                 i -> Arrays.equals(in.readBytes().getBytes(), fixed[i]));
        }

        int[] floats = {0x80000000, 0x3fc00000, 0x7f800000};
        try (PlainValuesWriter out = writer()) {
            for (int bits32 : floats) out.writeFloat(Float.intBitsToFloat(bits32));
            var in = new FloatPlainValuesReader();
            emit("FLOAT", out, in, floats.length,
                 i -> Float.floatToRawIntBits(in.readFloat()) == floats[i]);
        }

        long[] doubles = {0x8000000000000000L, 0x3ff8000000000000L, 0xfff0000000000000L};
        try (PlainValuesWriter out = writer()) {
            for (long bits64 : doubles) out.writeDouble(Double.longBitsToDouble(bits64));
            var in = new DoublePlainValuesReader();
            emit("DOUBLE", out, in, doubles.length,
                 i -> Double.doubleToRawLongBits(in.readDouble()) == doubles[i]);
        }
    }
}
