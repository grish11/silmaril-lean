import java.nio.file.Path;
import java.util.Map;
import org.apache.parquet.bytes.BytesInput;
import org.apache.parquet.bytes.HeapByteBufferAllocator;
import org.apache.parquet.column.Encoding;
import org.apache.parquet.column.values.bitpacking.ByteBitPackingValuesWriter;
import org.apache.parquet.column.values.bitpacking.Packer;
import org.apache.parquet.column.values.plain.PlainValuesWriter;
import org.apache.parquet.hadoop.ParquetFileWriter;
import org.apache.parquet.hadoop.metadata.CompressionCodecName;
import org.apache.parquet.io.LocalOutputFile;
import org.apache.parquet.schema.MessageTypeParser;

@SuppressWarnings("deprecation")
class LegacyBitPackedV1Writer {
    public static void main(String[] args) throws Exception {
        Integer[] values = {17, null, -9, 300, null, null, 0, null, Integer.MIN_VALUE};
        var schema = MessageTypeParser.parseMessageType("message schema { optional int32 v; }");
        var column = schema.getColumns().getFirst();
        var definitions = new ByteBitPackingValuesWriter(column.getMaxDefinitionLevel(), Packer.BIG_ENDIAN);
        try (var plain = new PlainValuesWriter(32, 64, HeapByteBufferAllocator.getInstance());
             var file = new ParquetFileWriter(new LocalOutputFile(Path.of(args[0])), schema,
                     ParquetFileWriter.Mode.OVERWRITE, 4096, 0, 64, 64, false)) {
            for (Integer value : values) {
                definitions.writeInteger(value == null ? 0 : 1);
                if (value != null) {
                    plain.writeInteger(value);
                }
            }
            // Flat schema has no repetition bytes. The producer supplies the
            // definitions and values and writes the actual V1 header and footer.
            BytesInput body = BytesInput.concat(definitions.getBytes(), plain.getBytes());
            file.start();
            file.startBlock(values.length);
            file.startColumn(column, values.length, CompressionCodecName.UNCOMPRESSED);
            file.writeDataPage(values.length, Math.toIntExact(body.size()), body,
                    Encoding.RLE, definitions.getEncoding(), plain.getEncoding());
            file.endColumn();
            file.endBlock();
            file.end(Map.of());
        }
    }
}
