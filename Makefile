.PHONY: all build build-release test clean fmt fmt-check clippy check doc doc-open ci help pkgconfig install

# Default target
all: build

# Build the project in debug mode
build:
	cd rust_accumulator && cargo build

# Build the project in release mode
build-release:
	cd rust_accumulator && cargo build --release

# Run tests
test:
	cd rust_accumulator && cargo test

# Format code using rustfmt
fmt:
	cd rust_accumulator && cargo fmt

# Check formatting
fmt-check:
	cd rust_accumulator && cargo fmt --check

# Run clippy linter
clippy:
	cd rust_accumulator && cargo clippy -- -D warnings

# Clean build artifacts
clean:
	cd rust_accumulator && cargo clean

# Check the project (quick verification without building)
check:
	cd rust_accumulator && cargo check

# Build documentation
doc:
	cd rust_accumulator && cargo doc --no-deps

# Open documentation in browser
doc-open:
	cd rust_accumulator && cargo doc --no-deps --open

# Run all checks (format, clippy, test)
ci: fmt-check clippy test

# Generate pkg-config file
pkgconfig: build-release
	@if [ -z "$$INSTALL" ]; then \
		echo "Error: INSTALL environment variable is not set."; \
		echo "Please set INSTALL to the installation directory, e.g.: export INSTALL=/usr/local"; \
		exit 1; \
	fi
	@mkdir -p rust_accumulator/target/pkgconfig
	@VERSION=$$(grep '^version' rust_accumulator/Cargo.toml | head -1 | cut -d'"' -f2); \
	sed -e "s|@PREFIX@|$$INSTALL|g" -e "s|@VERSION@|$$VERSION|g" \
		librust_accumulator.pc.in > rust_accumulator/target/pkgconfig/librust_accumulator.pc
	@echo "pkg-config file created at rust_accumulator/target/pkgconfig/librust_accumulator.pc"

# Install library and pkg-config file
install: build-release pkgconfig
	@if [ -z "$$INSTALL" ]; then \
		echo "Error: INSTALL environment variable is not set."; \
		echo "Please set INSTALL to the installation directory, e.g.: export INSTALL=/usr/local"; \
		exit 1; \
	fi
	@echo "Installing to: $$INSTALL"
	install -d $$INSTALL/lib
	install -m 644 rust_accumulator/target/release/librust_accumulator.a $$INSTALL/lib/
	install -d $$INSTALL/lib/pkgconfig
	install -m 644 rust_accumulator/target/pkgconfig/librust_accumulator.pc $$INSTALL/lib/pkgconfig/
	@echo "Installation complete. Library installed to $$INSTALL/lib/"

# Show help
help:
	@echo "Available targets:"
	@echo "  all           - Build the project in debug mode (default)"
	@echo "  build         - Build the project in debug mode"
	@echo "  build-release - Build the project in release mode"
	@echo "  test          - Run tests"
	@echo "  fmt           - Format code using rustfmt"
	@echo "  fmt-check     - Check if code is formatted correctly"
	@echo "  clippy        - Run clippy linter"
	@echo "  check         - Quick check without building"
	@echo "  clean         - Clean build artifacts"
	@echo "  doc           - Build documentation"
	@echo "  doc-open      - Build and open documentation in browser"
	@echo "  ci            - Run all checks (format, clippy, test)"
	@echo "  pkgconfig     - Generate pkg-config file (requires INSTALL env var)"
	@echo "  install       - Install library and pkg-config file (requires INSTALL env var)"
	@echo "  help          - Show this help message"
