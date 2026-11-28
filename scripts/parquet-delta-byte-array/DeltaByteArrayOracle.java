import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.HexFormat;

import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.delta.DeltaBinaryPackingValuesReader;
import org.apache.parquet.column.values.deltastrings.DeltaByteArrayReader;
import org.apache.parquet.column.values.deltastrings.DeltaByteArrayWriter;
import org.apache.parquet.io.api.Binary;

/** Emits scalar bytes and independently locates both boundaries with parquet-java 1.16.0. */
public class DeltaByteArrayOracle {
    private static int commonPrefix(byte[] previous, byte[] value) {
        int length = 0;
        while (length < Math.min(previous.length, value.length) && previous[length] == value[length]) {
            ++length;
        }
        return length;
    }

    private static void emit(String name, byte[][] values) throws IOException {
        var allocator = HeapByteBufferAllocator.getInstance();
        try (var writer = new DeltaByteArrayWriter(64, 4096, allocator)) {
            for (byte[] value : values) writer.writeBytes(Binary.fromConstantByteArray(value));
            if (writer.getEncoding() != Encoding.DELTA_BYTE_ARRAY) {
                throw new AssertionError(writer.getEncoding());
            }
            var output = new ByteArrayOutputStream();
            writer.getBytes().writeAllTo(output);
            byte[] encoded = output.toByteArray();
            var in = ByteBufferInputStream.wrap(ByteBuffer.wrap(encoded));
            var prefixReader = new DeltaBinaryPackingValuesReader();
            prefixReader.initFromPage(values.length, in);
            int prefixEnd = Math.toIntExact(in.position());
            var suffixLengthReader = new DeltaBinaryPackingValuesReader();
            suffixLengthReader.initFromPage(values.length, in);
            int payloadStart = Math.toIntExact(in.position());

            var fullReader = new DeltaByteArrayReader();
            fullReader.initFromPage(values.length, ByteBufferInputStream.wrap(ByteBuffer.wrap(encoded)));
            var payload = new ByteArrayOutputStream();
            byte[] previous = new byte[0];
            for (byte[] value : values) {
                int prefix = commonPrefix(previous, value);
                int suffix = value.length - prefix;
                if (prefixReader.readInteger() != prefix || suffixLengthReader.readInteger() != suffix ||
                        !Arrays.equals(fullReader.readBytes().getBytes(), value)) {
                    throw new AssertionError(name + " readback");
                }
                payload.write(value, prefix, suffix);
                previous = value;
            }
            if (!Arrays.equals(Arrays.copyOfRange(encoded, payloadStart, encoded.length), payload.toByteArray())) {
                throw new AssertionError(name + " payload boundary");
            }
            System.out.printf("%s\t%d\t%d\t%d\t%s%n", name, values.length, prefixEnd, payloadStart,
                    HexFormat.of().formatHex(encoded));
        }
    }

    public static void main(String[] args) throws IOException {
        var hex = HexFormat.of();
        emit("empty", new byte[0][]);
        emit("singleton-empty", new byte[][] {new byte[0]});
        emit("spec", Arrays.stream(new String[] {"axis", "axle", "babble", "babyhood"})
                .map(value -> value.getBytes(StandardCharsets.US_ASCII)).toArray(byte[][]::new));
        emit("opaque", new byte[][] {new byte[0], hex.parseHex("ff0080"), hex.parseHex("ff0081"),
            hex.parseHex("ff0081"), new byte[0], hex.parseHex("00ff"), hex.parseHex("00ff00")});
        byte[] repeated = new byte[130];
        Arrays.fill(repeated, (byte) 0xab);
        byte[] changed = repeated.clone();
        changed[changed.length - 1] = (byte) 0xff;
        emit("repeated", new byte[][] {repeated, repeated, changed, changed});
        byte[][] blocks = new byte[140][];
        for (int i = 0; i < blocks.length; ++i) {
            blocks[i] = new byte[] {(byte) 0xff, 0, (byte) (i / 2)};
        }
        emit("blocks", blocks);
    }
}
