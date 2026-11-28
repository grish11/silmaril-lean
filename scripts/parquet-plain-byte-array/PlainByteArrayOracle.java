import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.HexFormat;

import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.plain.BinaryPlainValuesReader;
import org.apache.parquet.column.values.plain.PlainValuesWriter;
import org.apache.parquet.io.api.Binary;

/** Independently writes and reads the present scalars in the mixed PyArrow pages. */
public class PlainByteArrayOracle {
    public static void main(String[] args) throws IOException {
        var hex = HexFormat.of();
        byte[][] values = {new byte[0], hex.parseHex("c3a9"), hex.parseHex("ff0080"), hex.parseHex("7879")};
        try (var writer = new PlainValuesWriter(64, 1024, HeapByteBufferAllocator.getInstance())) {
            for (byte[] value : values) writer.writeBytes(Binary.fromConstantByteArray(value));
            if (writer.getEncoding() != Encoding.PLAIN) throw new AssertionError(writer.getEncoding());
            var output = new ByteArrayOutputStream();
            writer.getBytes().writeAllTo(output);
            byte[] encoded = output.toByteArray();
            var reader = new BinaryPlainValuesReader();
            reader.initFromPage(values.length, ByteBufferInputStream.wrap(ByteBuffer.wrap(encoded)));
            for (byte[] value : values) {
                if (!Arrays.equals(value, reader.readBytes().getBytes())) throw new AssertionError("readback");
            }
            System.out.println(hex.formatHex(encoded));
        }
    }
}
