FROM oak-coq:latest
RUN rm -rf /home/coq/oak_coq
WORKDIR /home/coq/work
CMD ["/bin/bash", "-l"]
