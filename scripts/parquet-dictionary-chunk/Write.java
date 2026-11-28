import java.nio.file.Path;

import org.apache.parquet.column.ParquetProperties.WriterVersion;
import org.apache.parquet.conf.PlainParquetConfiguration;
import org.apache.parquet.example.data.simple.SimpleGroupFactory;
import org.apache.parquet.hadoop.example.ExampleParquetWriter;
import org.apache.parquet.hadoop.metadata.CompressionCodecName;
import org.apache.parquet.io.LocalOutputFile;
import org.apache.parquet.schema.MessageTypeParser;

/** Reproduce the complete parquet-java 1.16.0 dictionary fixtures. */
class Write {
    public static void main(String[] args) throws Exception {
        var schema = MessageTypeParser.parseMessageType(
                "message dictionary { required int32 required_i32; optional int32 optional_i32; }");
        var factory = new SimpleGroupFactory(schema);
        for (var version : WriterVersion.values()) {
            String suffix = version == WriterVersion.PARQUET_1_0 ? "v1" : "v2";
            var path = Path.of(args[0], "java-" + suffix + ".parquet");
            try (var writer = ExampleParquetWriter.builder(new LocalOutputFile(path))
                    .withConf(new PlainParquetConfiguration())
                    .withType(schema)
                    .withWriterVersion(version)
                    .withDictionaryEncoding(true)
                    .withCompressionCodec(CompressionCodecName.UNCOMPRESSED)
                    .withPageWriteChecksumEnabled(false)
                    .withPageRowCountLimit(64)
                    .build()) {
                for (int i = 0; i < 192; i++) {
                    var row = factory.newGroup().append("required_i32", 17 - 11 * (i % 3));
                    if (i % 4 != 0) {
                        row.append("optional_i32", -9 + 7 * (i % 5));
                    }
                    writer.write(row);
                }
            }
        }
    }
}
