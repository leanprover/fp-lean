FROM fedora:latest
RUN dnf install -y git
COPY . /lean-book
WORKDIR /lean-book/cmdline
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf > elan-init.sh
RUN chmod +x elan-init.sh
RUN ./elan-init.sh -y
RUN echo $PATH
ENV PATH="/root/.elan/bin:$PATH"
RUN echo $PATH
WORKDIR /lean-book
RUN elan default `cat lean-toolchain`
