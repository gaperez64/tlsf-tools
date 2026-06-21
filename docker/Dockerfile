# syntax=docker/dockerfile:1
#
# spot-syntcomp — a SYNTCOMP image that bundles
#   * ltlsynt / ltlfsynt from Spot (the synthesis backend), and
#   * the tlsf-tools decomposed-synthesis PREPROCESSOR (templates + in-process
#     OxiDD safety/GR(1) solvers) which carves clusters off a TLSF spec and
#     forwards only the hard liveness residual to ltlsynt.
#
# Derived from the upstream spot-syntcomp image
# (https://gitlab.lre.epita.fr/spot/syntcomp25); the Spot build stage mirrors it.
#
# Entry points (SYNTCOMP contract: REALIZABLE / UNREALIZABLE on stdout, AIGER
# model after REALIZABLE for the synthesis track):
#   spot-syntcomp-syn  SPEC.tlsf   — preprocessor + ltlsynt, emits a controller
#   spot-syntcomp-real SPEC.tlsf   — realizability only
# ltlsynt / ltlfsynt remain available directly for the non-preprocessed configs.
#
# Build from the repo root (the OxiDD submodule must be checked out):
#   docker build -f docker/Dockerfile -t spot-syntcomp .

# ---------------------------------------------------------------------------
# Stage 1 — Spot (ltlsynt / ltlfsynt).  Single optimized LTO pass; the upstream
# image additionally does a profile-guided two-pass build (run its full test
# suite to collect profiles) for ~10-20% more speed.  We keep one pass for a
# reliable, ~30-min CD build; bump SPOT_VERSION to track Spot.
# ---------------------------------------------------------------------------
FROM gcc:16.1-trixie AS spot-build
ARG SPOT_VERSION=2.15.1
ADD https://www.lre.epita.fr/dload/spot/spot-${SPOT_VERSION}.tar.gz /
RUN tar xf spot-${SPOT_VERSION}.tar.gz && cd /spot-${SPOT_VERSION} && \
    ./configure --disable-devel --disable-shared --enable-optimizations \
      --disable-python --prefix /usr \
      LDFLAGS=-fuse-linker-plugin NM=gcc-nm AR=gcc-ar ARFLAGS=cr AR_FLAGS=cr \
      RANLIB=gcc-ranlib VALGRIND=false \
      CFLAGS="-flto=auto" CXXFLAGS="-flto=auto" && \
    make -j"$(nproc)" AM_V_CXXLD=+ AM_V_CCLD=+ && \
    make install-strip

# ---------------------------------------------------------------------------
# Stage 2 — the tlsf-tools preprocessor, with the in-process OxiDD backend.
# Built on the same Debian release as the runtime so the binaries link cleanly.
# ---------------------------------------------------------------------------
FROM rust:1-trixie AS tlsf-build
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential meson ninja-build flex bison pkg-config python3 \
      ca-certificates && \
    rm -rf /var/lib/apt/lists/*
RUN cargo install cbindgen --locked
WORKDIR /src
COPY . .
# Vendored OxiDD C FFI (static lib + cbindgen header), then the OxiDD-enabled
# release build of the stable tlsf tools used by the preprocessor image.
RUN scripts/build_oxidd.sh && \
    meson setup build-oxidd -Doxidd=enabled -Dresearch_tools=false --buildtype=release && \
    ninja -C build-oxidd

# ---------------------------------------------------------------------------
# Stage 3 — slim runtime: ltlsynt + the preprocessor tools + SYNTCOMP wrappers.
# ---------------------------------------------------------------------------
FROM debian:13.5-slim
# Spot's C++ runtime + libgcc (also satisfies tlsfcompose's libgcc_s); make the
# loader search /usr/local/lib64 for them.
COPY --from=spot-build /usr/local/lib64/libstdc++.so* \
     /usr/local/lib64/libgcc_s.so* /usr/local/lib64/
RUN echo /usr/local/lib64 > /etc/ld.so.conf.d/spot.conf && ldconfig
COPY --from=spot-build /usr/bin/ltl*synt /usr/bin/
COPY --from=tlsf-build \
     /src/build-oxidd/tlsfcompose /src/build-oxidd/tlsfsolve \
     /src/build-oxidd/tlsfresidual /src/build-oxidd/tlsfnorm \
     /src/build-oxidd/tlsf2ltl /src/build-oxidd/tlsf2tlsf \
     /src/build-oxidd/tlsfinfo \
     /usr/bin/
COPY docker/spot-syntcomp-syn docker/spot-syntcomp-real /usr/bin/
RUN chmod +x /usr/bin/spot-syntcomp-syn /usr/bin/spot-syntcomp-real
CMD ["/bin/bash"]
