FROM oak-coq-toolchain

ARG CLAUDE_CODE_VERSION=2.1.301
ARG COQ_LSP_VERSION=0.2.5+8.20
ARG ROCQ_MCP_COMMIT=ee6d2c2d9f7acda80a5a5c893de608763a2597a9

USER root
RUN apt-get update && apt-get install -y --no-install-recommends python3-venv \
    && rm -rf /var/lib/apt/lists/*

USER coq
ENV OPAM_SWITCH_PREFIX=/home/coq/.opam/4.13.1+flambda
ENV PATH=/home/coq/.local/bin:/home/coq/.opam/4.13.1+flambda/bin:$PATH

# coq-lsp needs a newer ocamlfind, so Coq gets rebuilt in this image only
RUN opam pin remove -n ocamlfind && opam install -y coq-lsp.${COQ_LSP_VERSION} && opam clean -a
RUN curl -fsSL https://claude.ai/install.sh | bash -s ${CLAUDE_CODE_VERSION}
RUN git clone -q https://github.com/LLM4Rocq/rocq-mcp /home/coq/rocq-mcp \
    && cd /home/coq/rocq-mcp && git checkout -q ${ROCQ_MCP_COMMIT} \
    && python3 -m venv .venv && .venv/bin/pip install -q .

# swap coqc and coqtop for the logging wrapper so every run is recorded
COPY --chown=coq:coq rocq-log /home/coq/rocq-log
RUN cd $OPAM_SWITCH_PREFIX/bin && for b in coqc coqtop; do mv $b $b.real && cp /home/coq/rocq-log $b; done
COPY --chown=coq:coq mcp.json /home/coq/mcp.json

WORKDIR /home/coq/work
