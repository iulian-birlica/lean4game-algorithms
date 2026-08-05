FROM node:20

WORKDIR /

COPY ./lean-toolchain /lean-toolchain

USER root

RUN apt-get update && \
    apt-get install -y curl && \
    apt-get install -y git && \
    apt-get install -y python3 && \
    apt-get clean

ENV ELAN_HOME=/usr/local/elan \
  PATH=/usr/local/elan/bin:$PATH

SHELL ["/bin/bash", "-euxo", "pipefail", "-c"]

RUN export LEAN_VERSION="$(cat /lean-toolchain)" && \
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION; \
    chmod -R a+w $ELAN_HOME; \
    elan --version; \
    lean --version; \
    leanc --version; \
    lake --version;
