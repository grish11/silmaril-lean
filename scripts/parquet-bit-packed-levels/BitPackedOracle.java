import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.stream.Collectors;
import org.apache.parquet.bytes.ByteBufferInputStream;
import org.apache.parquet.column.ColumnDescriptor;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.ValuesType;
import org.apache.parquet.column.values.ValuesReader;
import org.apache.parquet.column.values.bitpacking.ByteBitPackingValuesWriter;
import org.apache.parquet.column.values.bitpacking.Packer;
import org.apache.parquet.schema.PrimitiveType.PrimitiveTypeName;

@SuppressWarnings("deprecation")
class BitPackedOracle {
    private static final HexFormat HEX = HexFormat.of();
    private static final byte[] SENTINEL = HEX.parseHex("a55a");

    private static void check(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }

    private static String hex(byte[] bytes) {
        return bytes.length == 0 ? "-" : HEX.formatHex(bytes);
    }

    private static void checkReader(String kind, String name, int maxLevel, byte[] packed,
                                    byte[] following, int... expected) throws Exception {
        var input = ByteBufferInputStream.wrap(ByteBuffer.wrap(packed), ByteBuffer.wrap(following));
        var descriptor = new ColumnDescriptor(new String[]{"v"}, PrimitiveTypeName.INT32, 0, maxLevel);
        ValuesReader reader = Encoding.BIT_PACKED.getValuesReader(descriptor, ValuesType.DEFINITION_LEVEL);
        reader.initFromPage(expected.length, input);
        for (int level : expected) {
            check(reader.readInteger() == level, name + " wrong readback");
        }
        check(input.position() == packed.length, name + " wrong consumed length");
        byte[] remainder = input.readAllBytes();
        check(Arrays.equals(remainder, following), name + " remainder was altered");
        String levels = Arrays.stream(expected).mapToObj(Integer::toString).collect(Collectors.joining(","));
        System.out.printf("%s\t%s\t%d\t%d\t%s\t%s\t%s%n", kind, name, maxLevel, expected.length,
                hex(packed), hex(remainder), levels.isEmpty() ? "-" : levels);
    }

    private static void emit(String name, int maxLevel, String expectedHex, int... levels)
            throws Exception {
        var writer = new ByteBitPackingValuesWriter(maxLevel, Packer.BIG_ENDIAN);
        for (int level : levels) {
            writer.writeInteger(level);
        }
        check(writer.getEncoding() == Encoding.BIT_PACKED, name + " wrong encoding");
        byte[] packed = writer.getBytes().toByteArray();
        check(HEX.formatHex(packed).equals(expectedHex), name + " unexpected producer bytes");
        checkReader("producer", name, maxLevel, packed, SENTINEL, levels);
    }

    public static void main(String[] args) throws Exception {
        emit("zero-width", 0, "", 0, 0, 0);
        emit("zero-count", 7, "");
        emit("nullable-mask", 1, "b0", 1, 0, 1, 1, 0);
        emit("non-power-of-two-bound", 2, "8600", 2, 0, 1, 2, 0);
        emit("spec-group", 7, "053977", 0, 1, 2, 3, 4, 5, 6, 7);
        emit("second-group", 7, "05397720", 0, 1, 2, 3, 4, 5, 6, 7, 1);
        emit("signed-max-level", Integer.MAX_VALUE, "fffffffe0000000000000008", Integer.MAX_VALUE, 0, 1);

        checkReader("consumer", "unused-low-bits", 1, HEX.parseHex("b7"), SENTINEL, 1, 0, 1, 1, 0);
        checkReader("consumer", "spare-code", 2, HEX.parseHex("c0"), SENTINEL, 3);
        checkReader("consumer", "truncated", 7, HEX.parseHex("053977"), new byte[0], 0, 1, 2, 3, 4, 5, 6, 7, 0);
    }
}
