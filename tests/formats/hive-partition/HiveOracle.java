import java.util.ArrayList;
import java.util.Locale;
import org.apache.hadoop.hive.common.FileUtils;

class HiveOracle {
    public static void main(String[] args) {
        Locale.setDefault(Locale.ROOT);
        var keys = new ArrayList<String>();
        var values = new ArrayList<String>();
        for (int i = 0; i < args.length; i += 3) {
            keys.add(args[i]);
            values.add(args[i + 1].equals("null") ? null : args[i + 2]);
        }
        System.out.println(FileUtils.makePartName(keys, values));
    }
}
