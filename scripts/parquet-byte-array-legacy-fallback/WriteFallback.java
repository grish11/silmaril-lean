import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.Locale;

import org.apache.parquet.column.ParquetProperties.WriterVersion;
import org.apache.parquet.conf.PlainParquetConfiguration;
import org.apache.parquet.example.data.simple.SimpleGroupFactory;
import org.apache.parquet.hadoop.example.ExampleParquetWriter;
import org.apache.parquet.hadoop.metadata.CompressionCodecName;
import org.apache.parquet.io.LocalOutputFile;
import org.apache.parquet.io.api.Binary;
import org.apache.parquet.schema.MessageTypeParser;

/** Produce same-chunk fallback from dictionary encoding. */
class WriteFallback {
    public static void main(String[] args) throws Exception {
        var schema = MessageTypeParser.parseMessageType(
                "message fallback { required int32 ordinal; optional binary payload; }");
        var factory = new SimpleGroupFactory(schema);
        var path = Path.of(args[0], "java-binary-fallback-v1.parquet");
        try (var writer = ExampleParquetWriter.builder(new LocalOutputFile(path))
                .withConf(new PlainParquetConfiguration())
                .withType(schema)
                .withWriterVersion(WriterVersion.PARQUET_1_0)
                .withDictionaryEncoding(true)
                .withDictionaryPageSize(96)
                .withCompressionCodec(CompressionCodecName.UNCOMPRESSED)
                .withPageWriteChecksumEnabled(false)
                .withPageRowCountLimit(16)
                .build()) {
            for (int i = 0; i < 384; i++) {
                var row = factory.newGroup().append("ordinal", i);
                if (i % 13 != 5) {
                    String value = i < 256 ? (i % 2 == 0 ? "repeat-a" : "repeat-b")
                        : String.format(Locale.ROOT, "distinct-%04d-", i) + "opaque-value-".repeat(4);
                    row.append("payload", Binary.fromConstantByteArray(value.getBytes(StandardCharsets.US_ASCII)));
                }
                writer.write(row);
            }
        }
    }
}
