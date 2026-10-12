# The Linux release's build machine (scripts/dist-linux): manylinux_2_28,
# glibc 2.28, so a tarball built here runs on any glibc as new or newer
# (Debian 10, Ubuntu 18.10, RHEL 8 and on), with gfortran 14 from
# gcc-toolset; babashka pinned to the version the scripts are run with.
ARG BASE=quay.io/pypa/manylinux_2_28_aarch64
FROM ${BASE}
RUN curl -sL https://raw.githubusercontent.com/babashka/babashka/master/install -o /tmp/bbi \
 && bash /tmp/bbi --version 1.3.185 && rm /tmp/bbi
WORKDIR /src
