FROM 		ubuntu:artful
MAINTAINER 	Mike Popoloski
CMD 		bash

RUN apt-get update && apt-get install -y \
	apt-utils \
	build-essential \
	curl \
	git \
	wget \
	doxygen \
	xz-utils \
	g++-7 \
	clang-5.0 \
	clang-tidy-5.0

RUN wget -O /tmp/cppcheck.tar.gz && \
	http://github.com/danmar/cppcheck/releases/download/1.81/cppcheck-1.81.tar.gz && \
	tar xvzf /tmp/cppcheck.tar.gz && \
	make -j 4 -C /tmp/cppcheck