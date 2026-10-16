FROM alpine:latest
RUN apk add --no-cache tinyproxy
COPY tinyproxy.conf blocked.txt /etc/tinyproxy/
CMD ["tinyproxy", "-d", "-c", "/etc/tinyproxy/tinyproxy.conf"]
