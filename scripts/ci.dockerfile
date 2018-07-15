FROM 		ubuntu:bionic
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
	g++-8 \
	clang-6.0 \
	clang-tidy-6.0 \
	cmake

RUN wget -O /tmp/cppcheck.tar.gz \
	https://github.com/danmar/cppcheck/archive/1.83.tar.gz && \
	mkdir -p /tmp/cppcheck && \
	tar xvzf /tmp/cppcheck.tar.gz -C /tmp/cppcheck --strip-components=1 && \
	make -j 4 -C /tmp/cppcheck