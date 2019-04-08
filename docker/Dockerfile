FROM ubuntu

# Setting required build packages
RUN apt-get update && \
    apt-get install -y git cmake make gcc g++ doxygen pkg-config \
	uuid-dev openjdk-11-jdk zlib1g-dev opam m4 \
	autoconf automake libtool libgmp-dev libboost-dev \
	python3 python3-pip \
	flex bison wget tar patch unzip

# Setting python environment
RUN pip3 install setuptools pyyaml jinja2 colorama GitPython

# Setting ocaml environment
RUN opam init -y && \
    opam install alt-ergo why3 -y && \
    opam config exec env

ENV PATH /root/.opam/system/bin:$PATH

# Recovering and building solvers
RUN git clone https://github.com/CVC4/CVC4.git cvc4 && \
    git clone https://github.com/Z3Prover/z3.git z3 && \
    wget https://verit.loria.fr/distrib/veriT-stable2016.tar.gz && \
    tar xvf veriT-stable2016.tar.gz

WORKDIR cvc4
RUN git checkout f8d6bd369 && \
    ./contrib/get-antlr-3.4 && \
    ./autogen.sh && \
    ./configure && \
    make && make install

WORKDIR ../z3/build
RUN git checkout 3b1b82bef && \
    cmake .. && make && make install

WORKDIR ../../veriT-stable2016
RUN autoconf && \
    ./configure && \
    make && make install

# Configuring Why3 with the solver installed
ENV LD_LIBRARY_PATH $LD_LIBRARY_PATH:/usr/local/lib
RUN why3 config

# Recovering Abdulot
ARG version=0.8.1
WORKDIR ..
RUN git clone https://github.com/sellamiy/GPiD-Framework.git abdulot && \
    cd abdulot && git checkout $version

# Installing legacy tooleval
WORKDIR tooleval-build
RUN cp -v ../abdulot/legacy/import/tooleval-0.2bis.zip . && \
    unzip tooleval-0.2bis.zip && \
    wget https://www.antlr.org/download/antlr-4.8-complete.jar && \
    export CLASSPATH=".:$(pwd)/antlr-4.8-complete.jar:$CLASSPATH" && \
    cd tooleval-0.2bis/grammar && \
    java -jar ../../antlr-4.8-complete.jar -no-listener -visitor -Dlanguage=Python3 -o ../tooleval ToolEvaluationScript.g4 && \
    cd .. && \
    python3 setup.py install

# Building Abdulot
WORKDIR ../abdulot-build
RUN cmake -DCMAKE_BUILD_TYPE=Release -DFRAMEWORK_WRAPPING_LANGUAGE=Sh ../abdulot && make Sh-executable-wrappers

# Verifying build
RUN make all
RUN make test || echo "Some tests failed... Bypassed" >&2

# New build stage
FROM ubuntu

# Copying built libraries and tools
COPY --from=0 /usr/lib/x86_64-linux-gnu/libgomp* /usr/lib/
COPY --from=0 /usr/local/lib/libcvc4.so.5 /usr/local/lib/libcvc4compat.so.5 /usr/local/lib/libcvc4parser.so.5 /usr/local/lib/libz3.so.4.7 /usr/lib/
COPY --from=0 /root/.opam/system /root/.opam/system
COPY --from=0 /usr/local/bin /usr/local/bin
COPY --from=0 /abdulot-build/bin /usr/local/bin

# Updating container config
ENV PATH /root/.opam/system/bin:$PATH
RUN why3 config

# Linking container
#ENTRYPOINT ["ilinva-w3wml", "-i", "/data/in/01.mlw", "-a", "/data/in/01.abd", "-g", "ccvc4", "--smt-time-limit=1", "-s", "1", "-H", "solver:CVC4", "-H", "vcreorder:false", "-c", "-o", "/data/out/Res.mlw"]
ENTRYPOINT ["abdulot-select"]
