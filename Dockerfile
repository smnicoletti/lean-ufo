# The base digest selects a multi-architecture Ubuntu 24.04 image. Lean and
# library revisions are fixed separately by lean-toolchain and lake-manifest.
FROM ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55 AS toolchain
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential ca-certificates curl git elan zstd \
    texlive-latex-base texlive-latex-recommended texlive-latex-extra \
    texlive-fonts-recommended && \
    apt-get clean
RUN useradd --create-home --uid 1001 --shell /bin/bash reviewer && \
    mkdir -p /workspace/alien /results /opt/alien && \
    chown reviewer:reviewer /workspace/alien /results /opt/alien
ENV PATH=/home/reviewer/.elan/bin:$PATH
ENV LEAN_NUM_THREADS=2
USER reviewer
WORKDIR /workspace/alien
COPY --chown=reviewer:reviewer lean-toolchain lakefile.toml lake-manifest.json ./
RUN elan toolchain install "$(cat lean-toolchain)"
COPY --chown=reviewer:reviewer artifact/dependency-sources.* /opt/alien/
RUN mkdir -p .lake/packages && \
    if [ -f /opt/alien/dependency-sources.tar.gz ]; then \
      tar -xzf /opt/alien/dependency-sources.tar.gz -C .lake/packages; \
    fi
RUN lake exe cache get

FROM toolchain AS compiled
# Keep prose and packaging edits from invalidating compiled Lean dependencies.
# The quickstart is included here because the full suite checks its example.
COPY --chown=reviewer:reviewer LeanUfo/ LeanUfo/
COPY --chown=reviewer:reviewer LeanUfo.lean LeanUfoTest.lean ./
COPY --chown=reviewer:reviewer docs/dsl/quickstart.md docs/dsl/quickstart.md
RUN lake build LeanUfo LeanUfoTest experiment-tables performance-experiments \
      complexity-benchmarks export-certificates validate-certificate \
      LeanUfo.UFO.DSL.Examples LeanUfo.Test.Certification.Positive.Relator && \
    lake exe experiment-tables --self-test && \
    LEANUFO_FULL_TESTS=1 lake test

FROM compiled AS artifact
ARG SOURCE_REVISION=unreleased-worktree
ENV ALIEN_SOURCE_REVISION=$SOURCE_REVISION
COPY --chown=reviewer:reviewer . .
# The reference run is historical evidence, never the destination of new runs.
RUN mkdir -p /opt/alien/reference && \
    tar -xzf artifact/reference-results.tar.gz -C /opt/alien/reference && \
    dpkg-query -W > /opt/alien/system-packages.txt && \
    chmod +x artifact/run.sh
ENV LEANUFO_EXPERIMENT_DIR=/results/experiments
ENTRYPOINT ["/workspace/alien/artifact/run.sh"]
CMD ["help"]
