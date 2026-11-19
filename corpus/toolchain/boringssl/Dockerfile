# Distinct extension of the unchanged standard corpus image. image.sh passes its
# verified immutable image ID. OS additions use the parent's pinned apt snapshot.
ARG CORPUS_BASE
FROM ${CORPUS_BASE}
RUN apt-get update \
 && apt-get install -y --no-install-recommends cmake=3.31.6-2 ninja-build=1.12.1-1 \
 && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL --max-time 120 https://go.dev/dl/go1.27.4.linux-amd64.tar.gz -o /tmp/go.tar.gz \
 && echo '7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840  /tmp/go.tar.gz' | sha256sum -c - \
 && tar -C /usr/local -xzf /tmp/go.tar.gz \
 && rm /tmp/go.tar.gz \
 && ln -s /usr/local/go/bin/go /usr/local/bin/go \
 && ln -s /usr/local/go/bin/gofmt /usr/local/bin/gofmt
COPY inventory.py /tmp/toolchain-inventory.py
RUN mkdir /toolchain \
 && python3 -I /tmp/toolchain-inventory.py /toolchain \
 && rm /tmp/toolchain-inventory.py
