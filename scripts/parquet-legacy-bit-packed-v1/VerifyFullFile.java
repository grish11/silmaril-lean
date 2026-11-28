import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Objects;
import org.apache.parquet.ParquetReadOptions;
import org.apache.parquet.VersionParser;
import org.apache.parquet.column.impl.ColumnReaderImpl;
import org.apache.parquet.conf.PlainParquetConfiguration;
import org.apache.parquet.hadoop.ParquetFileReader;
import org.apache.parquet.io.LocalInputFile;
import org.apache.parquet.io.api.PrimitiveConverter;

class VerifyFullFile {
    public static void main(String[] args) throws Exception {
        var input = new LocalInputFile(Path.of(args[0]));
        var options = ParquetReadOptions.builder(new PlainParquetConfiguration()).build();
        try (var file = ParquetFileReader.open(input, options);
             var group = file.readNextRowGroup()) {
            var metadata = file.getFileMetaData();
            var leaf = metadata.getSchema().getColumns().getFirst();
            var reader = new ColumnReaderImpl(leaf, group.getPageReader(leaf),
                    new PrimitiveConverter() {}, VersionParser.parse(metadata.getCreatedBy()));
            var values = new ArrayList<Integer>();
            for (long i = 0; i < group.getRowCount(); i++) {
                if (reader.getCurrentRepetitionLevel() != 0) {
                    throw new AssertionError("repetition level");
                }
                values.add(reader.getCurrentDefinitionLevel() == 1 ? reader.getInteger() : null);
                reader.consume();
            }
            var expected = Arrays.asList(17, null, -9, 300, null, null, 0, null, Integer.MIN_VALUE);
            if (!Objects.equals(values, expected) || file.readNextRowGroup() != null) {
                throw new AssertionError("unexpected row groups or values " + values);
            }
            System.out.println(values);
        }
    }
}
