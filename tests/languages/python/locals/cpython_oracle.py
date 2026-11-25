"""Independent CPython outcomes for the integer-local frame regression."""

import sys


def copy_then_overwrite():
    x = 7 // -3
    y = x
    x = 2 + 5
    return y


def self_read_before_write():
    x = x
    return x


def failed_reassignment():
    x = 5
    y = 8
    x = 1 // 0
    return y


def local_operands():
    x = -3
    y = 7
    return y // x + y


def read_before_division():
    x = x + (1 // 0)
    return x


def division_before_read():
    x = (1 // 0) + x
    return x


def negative_condition():
    x = -9
    if x:
        return 2 + 5
    return 1 // 0


def zero_condition():
    x = 0
    if x:
        return 1 // 0
    return 8


def failing_condition():
    x = 1
    if x // 0:
        return 2 + 5
    return 8


def false_and():
    x = 0
    return x and (1 // 0)


def true_or():
    x = -4
    return x or (1 // 0)


def true_and():
    x = 7
    return x and (1 // 0)


def false_or():
    x = 0
    return x or (7 // -3)


def main():
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 12, 13):
        raise SystemExit("Expected CPython 3.12.13")
    for body in (
        copy_then_overwrite,
        self_read_before_write,
        failed_reassignment,
        local_operands,
        read_before_division,
        division_before_read,
        negative_condition,
        zero_condition,
        failing_condition,
        false_and,
        true_or,
        true_and,
        false_or,
    ):
        try:
            outcome = body()
        except (UnboundLocalError, ZeroDivisionError) as error:
            outcome = type(error).__name__
        print(f"parity\t{body.__name__}\t{outcome}")


if __name__ == "__main__":
    main()
