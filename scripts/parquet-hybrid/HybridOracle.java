import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.HexFormat;

import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.values.rle.RunLengthBitPackingHybridDecoder;
import org.apache.parquet.column.values.rle.RunLengthBitPackingHybridEncoder;

/** Emits raw encoded-data slices with parquet-java 1.16.0 and checks its decoder. */
public class HybridOracle {
    private static void emit(String name, int width, int[] values) throws IOException {
        try (var encoder = new RunLengthBitPackingHybridEncoder(
                width, 64, 1024, HeapByteBufferAllocator.getInstance())) {
            for (int value : values) {
                encoder.writeInt(value);
            }
            var output = new ByteArrayOutputStream();
            encoder.toBytes().writeAllTo(output);
            byte[] bytes = output.toByteArray();
            var input = new ByteArrayInputStream(bytes);
            var decoder = new RunLengthBitPackingHybridDecoder(width, input);
            for (int i = 0; i < values.length; ++i) {
                if (decoder.readInt() != values[i]) {
                    throw new AssertionError(name + " value " + i);
                }
            }
            if (input.available() != 0) {
                throw new AssertionError(name + " left raw bytes unread");
            }
            System.out.printf("%s\t%d\t%d\t%s%n",
                name, width, values.length, HexFormat.of().formatHex(bytes));
        }
    }

    public static void main(String[] args) throws IOException {
        int[] repeated = new int[130];
        Arrays.fill(repeated, 19);
        emit("rle", 5, repeated);
        emit("packed", 3, new int[] {0, 1, 2, 3, 4, 5, 6, 7, 5, 2, 3});

        int[] mixed = new int[31];
        for (int i = 0; i < 8; ++i) {
            mixed[i] = i;
        }
        Arrays.fill(mixed, 8, 28, 5);
        mixed[28] = 0;
        mixed[29] = 2;
        mixed[30] = 6;
        emit("mixed", 3, mixed);

        emit("zero-width", 0, new int[11]);
        int[] fullWidth = new int[8];
        Arrays.fill(fullWidth, -1);
        emit("width32", 32, fullWidth);
    }
}
