# Toolchain image for corpus (every package, both architectures).
# Base: debian:trixie-20251103 pinned by digest; apt pointed at snapshot.debian.org at
# 20251103T000000Z so the installed package versions are fixed (exact versions: lock.txt).
# Build with ./image.sh (tag silmaril-corpus-toolchain:trixie-20251103).
FROM debian:trixie-20251103@sha256:01a723bf5bfb21b9dda0c9a33e0538106e4d02cce8f557e118dd61259553d598
ENV DEBIAN_FRONTEND=noninteractive LC_ALL=C.UTF-8 TZ=UTC
RUN rm -f /etc/apt/sources.list.d/debian.sources \
 && printf '%s\n' \
    'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/20251103T000000Z trixie main' \
    'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/20251103T000000Z trixie-updates main' \
    'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian-security/20251103T000000Z trixie-security main' \
    > /etc/apt/sources.list \
 && printf 'Acquire::Check-Valid-Until "false";\nAcquire::Retries "5";\n' > /etc/apt/apt.conf.d/99snapshot \
 && apt-get update \
 && apt-get install -y --no-install-recommends \
    build-essential gcc-aarch64-linux-gnu g++-aarch64-linux-gnu libc6-dev-arm64-cross \
    binutils-aarch64-linux-gnu qemu-user make perl python3 pkg-config file xz-utils bzip2 \
    unzip ca-certificates curl gpg gpgv \
 && rm -rf /var/lib/apt/lists/*
