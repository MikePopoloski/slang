FROM 		ubuntu:cosmic
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
	clang-7 \
	clang-tidy-7 \
	cmake \
	python3 \
	python3-distutils \
	python3-setuptools \
	python3-pip

RUN pip3 install conan && conan user

RUN wget -O /tmp/cppcheck.tar.gz \
	https://github.com/danmar/cppcheck/archive/1.84.tar.gz && \
	mkdir -p /tmp/cppcheck && \
	tar xvzf /tmp/cppcheck.tar.gz -C /tmp/cppcheck --strip-components=1 && \
	make -j 4 -C /tmp/cppcheck