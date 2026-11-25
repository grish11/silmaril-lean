import java.nio.file.Files;
import java.nio.file.Path;
import tla2sany.output.SimpleSanyOutput;
import tla2sany.output.LogLevel;
import tla2sany.parser.TLAplusParser;

/** Syntax-only oracle. Calling SANY's frontend would also try to resolve imports. */
public final class SanySyntax {
    public static void main(String[] args) throws Exception {
        boolean matches = true;
        for (int i = 0; i < args.length; i += 2) {
            Path path = Path.of(args[i]);
            boolean expected = args[i + 1].equals("accept");
            System.out.println(path.getFileName() + ": expected " + args[i + 1]);
            var parser = new TLAplusParser(
                new SimpleSanyOutput(System.out, LogLevel.ERROR), Files.readAllBytes(path));
            boolean actual = parser.parse();
            if (actual != expected) {
                System.err.println(path + ": unexpected syntax verdict " + actual);
                matches = false;
            }
        }
        if (!matches) System.exit(1);
    }
}
