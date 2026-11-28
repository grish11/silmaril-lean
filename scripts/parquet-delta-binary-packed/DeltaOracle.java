import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.HexFormat;
import java.util.stream.IntStream;

import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.delta.DeltaBinaryPackingValuesReader;
import org.apache.parquet.column.values.delta.DeltaBinaryPackingValuesWriterForInteger;
import org.apache.parquet.column.values.delta.DeltaBinaryPackingValuesWriterForLong;

/** Emits scalar slices from parquet-java 1.16.0 after independent reader round trips. */
public class DeltaOracle {
    private static void emit(String physical, String name, int size, int minis, long[] values)
            throws IOException {
        var allocator = HeapByteBufferAllocator.getInstance();
        boolean int32 = physical.equals("INT32");
        try (var writer = int32 ?
                new DeltaBinaryPackingValuesWriterForInteger(size, minis, 64, 4096, allocator) :
                new DeltaBinaryPackingValuesWriterForLong(size, minis, 64, 4096, allocator)) {
            for (long value : values) {
                if (int32) writer.writeInteger(Math.toIntExact(value));
                else writer.writeLong(value);
            }
            if (writer.getEncoding() != Encoding.DELTA_BINARY_PACKED) {
                throw new AssertionError(writer.getEncoding());
            }
            var output = new ByteArrayOutputStream();
            writer.getBytes().writeAllTo(output);
            byte[] bytes = output.toByteArray();
            var reader = new DeltaBinaryPackingValuesReader();
            reader.initFromPage(values.length, ByteBufferInputStream.wrap(ByteBuffer.wrap(bytes)));
            for (long value : values) {
                if ((int32 ? reader.readInteger() : reader.readLong()) != value) {
                    throw new AssertionError(name + " readback");
                }
            }
            System.out.printf("%s\t%s\t%d\t%d\t%d\t%s%n", physical, name, size, minis,
                    values.length, HexFormat.of().formatHex(bytes));
        }
    }

    public static void main(String[] args) throws IOException {
        emit("INT32", "empty", 128, 4, new long[0]);
        emit("INT32", "singleton", 128, 4, new long[] {Integer.MIN_VALUE});
        emit("INT32", "wrap", 128, 4,
                new long[] {0, Integer.MIN_VALUE, -1, Integer.MAX_VALUE, 0, Integer.MIN_VALUE, 0});
        emit("INT32", "blocks", 128, 4,
                IntStream.range(0, 140).mapToLong(i -> 1000 - 3 * i + i % 5).toArray());
        emit("INT64", "wrap", 128, 4,
                new long[] {0, Long.MIN_VALUE, -1, Long.MAX_VALUE, 0, Long.MIN_VALUE, 0});
        emit("INT64", "wide-miniblock", 256, 2,
                new long[] {5000000000L, 4999999997L, 4999999994L, 4999999991L});
    }
}
