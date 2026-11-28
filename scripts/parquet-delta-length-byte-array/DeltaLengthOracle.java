import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.HexFormat;

import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.delta.DeltaBinaryPackingValuesReader;
import org.apache.parquet.column.values.deltalengthbytearray.DeltaLengthByteArrayValuesReader;
import org.apache.parquet.column.values.deltalengthbytearray.DeltaLengthByteArrayValuesWriter;
import org.apache.parquet.io.api.Binary;

/** Emits scalar slices after checking their lengths and bytes with parquet-java 1.16.0. */
public class DeltaLengthOracle {
    private static void emit(String name, byte[][] values) throws IOException {
        var hex = HexFormat.of();
        var allocator = HeapByteBufferAllocator.getInstance();
        try (var writer = new DeltaLengthByteArrayValuesWriter(64, 4096, allocator)) {
            var payload = new ByteArrayOutputStream();
            for (byte[] value : values) {
                writer.writeBytes(Binary.fromConstantByteArray(value));
                payload.writeBytes(value);
            }
            if (writer.getEncoding() != Encoding.DELTA_LENGTH_BYTE_ARRAY) {
                throw new AssertionError(writer.getEncoding());
            }
            var output = new ByteArrayOutputStream();
            writer.getBytes().writeAllTo(output);
            byte[] encoded = output.toByteArray();

            var lengthInput = ByteBufferInputStream.wrap(ByteBuffer.wrap(encoded));
            var lengthReader = new DeltaBinaryPackingValuesReader();
            lengthReader.initFromPage(values.length, lengthInput);
            int split = Math.toIntExact(lengthInput.position());
            if (!Arrays.equals(Arrays.copyOfRange(encoded, split, encoded.length), payload.toByteArray())) {
                throw new AssertionError(name + " payload boundary");
            }

            var reader = new DeltaLengthByteArrayValuesReader();
            reader.initFromPage(values.length, ByteBufferInputStream.wrap(ByteBuffer.wrap(encoded)));
            for (byte[] value : values) {
                if (lengthReader.readInteger() != value.length || !Arrays.equals(reader.readBytes().getBytes(), value)) {
                    throw new AssertionError(name + " readback");
                }
            }
            System.out.printf("%s\t%d\t%d\t%s%n", name, values.length, split, hex.formatHex(encoded));
        }
    }

    public static void main(String[] args) throws IOException {
        var hex = HexFormat.of();
        emit("empty", new byte[0][]);
        emit("singleton-empty", new byte[][] {new byte[0]});
        emit("mixed", new byte[][] {
            hex.parseHex("61"), new byte[0], hex.parseHex("c3a9"), hex.parseHex("ff0080"), hex.parseHex("00")
        });
        byte[] longValue = new byte[130];
        Arrays.fill(longValue, (byte) 0xab);
        emit("long", new byte[][] {longValue, new byte[0], hex.parseHex("7f00")});
        byte[][] blocks = new byte[140][];
        for (int i = 0; i < blocks.length; ++i) {
            blocks[i] = i % 4 == 0 ? new byte[] {(byte) i} : new byte[0];
        }
        emit("blocks", blocks);
    }
}
