FROM leanprovercommunity/lean4

USER root
RUN apt-get update
RUN apt-get install -y gcc tmux vim tree
RUN rm -rf /var/lib/apt/lists/*

USER lean
ENV http_proxy=192.168.31.2:10801
ENV http_proxys=192.168.31.2:10801
RUN elan self update
RUN elan toolchain install leanprover/lean4:v4.21.0

