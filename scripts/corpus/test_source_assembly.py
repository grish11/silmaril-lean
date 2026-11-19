import unittest
from source_assembly import volatile_asm_sites


class SourceAssembly(unittest.TestCase):
    def test_source_syntax_separate_from_comments_and_compiler_asm_strings(self):
        text = '''// asm volatile("not code");
const char *command = "__asm__ __volatile__(fake)";
/* __asm__ __volatile__(also not code); */
void f(void) {
    __asm__ __volatile__("nop" : : : "memory");
    asm volatile ("pause");
    __asm__("nonvolatile form intentionally unclassified");
}
'''
        self.assertEqual([s['line'] for s in volatile_asm_sites(text)], [5, 6])

    def test_conditional_site_is_reported_without_assuming_active_preprocessing(self):
        text = '#if 0\n__asm__\n __volatile__("nop");\n#endif\n'
        self.assertEqual([s['line'] for s in volatile_asm_sites(text)], [2])


if __name__ == '__main__':
    unittest.main()
