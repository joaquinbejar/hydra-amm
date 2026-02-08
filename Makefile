# =============================================================================
# Makefile for Hydra AMM
# Universal AMM engine library crate
# =============================================================================

# Detect current branch
CURRENT_BRANCH := $(shell git rev-parse --abbrev-ref HEAD)

# Project name
PROJECT_NAME := hydra-amm

# =============================================================================
# Default target
# =============================================================================
.PHONY: all
all: fmt lint test build

# =============================================================================
# Build
# =============================================================================

.PHONY: build
build:
	@echo "Building debug version..."
	cargo build --all-features

.PHONY: build-no-std
build-no-std:
	@echo "Building with no default features (no_std check)..."
	cargo build --no-default-features

.PHONY: build-features
build-features:
	@echo "Building feature combinations..."
	cargo build --no-default-features
	cargo build --no-default-features --features constant-product
	cargo build --no-default-features --features clmm
	cargo build --no-default-features --features "fixed-point,constant-product"
	cargo build --all-features
	@echo "All feature combinations built successfully!"

.PHONY: release
release:
	@echo "Building release version..."
	cargo build --release --all-features

.PHONY: clean
clean:
	@echo "Cleaning build artifacts..."
	cargo clean

# =============================================================================
# Test & Quality
# =============================================================================

.PHONY: test
test:
	@echo "Running all tests..."
	RUST_LOG=warn cargo test --all-features

.PHONY: test-lib
test-lib:
	@echo "Running library tests..."
	RUST_LOG=warn cargo test --lib --all-features

.PHONY: test-doc
test-doc:
	@echo "Running documentation tests..."
	cargo test --doc --all-features

.PHONY: fmt
fmt:
	@echo "Formatting code..."
	cargo +stable fmt --all

.PHONY: fmt-check
fmt-check:
	@echo "Checking code formatting..."
	cargo +stable fmt --all --check

.PHONY: lint
lint:
	@echo "Running clippy lints..."
	cargo clippy --all-targets --all-features -- -D warnings

.PHONY: lint-no-std
lint-no-std:
	@echo "Running clippy lints (no default features)..."
	cargo clippy --all-targets --no-default-features -- -D warnings

.PHONY: lint-fix
lint-fix:
	@echo "Auto-fixing lint issues..."
	cargo clippy --fix --all-targets --all-features --allow-dirty --allow-staged -- -D warnings

.PHONY: fix
fix:
	@echo "Applying cargo fix suggestions..."
	cargo fix --allow-staged --allow-dirty

.PHONY: check
check: fmt-check lint lint-no-std test
	@echo "All checks passed!"

.PHONY: pre-push
pre-push: fix fmt lint-fix test doc
	@echo "All pre-push checks passed!"

# =============================================================================
# Documentation
# =============================================================================

.PHONY: doc
doc:
	@echo "Generating documentation..."
	cargo doc --no-deps --document-private-items

.PHONY: doc-open
doc-open:
	@echo "Opening documentation in browser..."
	cargo doc --no-deps --all-features --open

.PHONY: doc-check
doc-check:
	@echo "Checking documentation builds without warnings..."
	RUSTDOCFLAGS="-D warnings" cargo doc --all-features --no-deps

# =============================================================================
# Packaging & Publishing
# =============================================================================

.PHONY: publish
publish:
	@echo "Publishing to crates.io (dry run)..."
	cargo publish --dry-run
	@echo "Dry run complete. Run 'cargo publish' to actually publish."

.PHONY: package
package:
	@echo "Listing package contents..."
	cargo package --list

# =============================================================================
# Coverage & Benchmarks
# =============================================================================

.PHONY: coverage
coverage:
	@echo "Generating code coverage report (XML)..."
	@command -v cargo-tarpaulin > /dev/null || cargo install cargo-tarpaulin
	@mkdir -p coverage
	RUST_LOG=warn cargo tarpaulin --verbose --all-features --timeout 120 --out xml --output-dir coverage

.PHONY: coverage-html
coverage-html:
	@echo "Generating HTML coverage report..."
	@command -v cargo-tarpaulin > /dev/null || cargo install cargo-tarpaulin
	@mkdir -p coverage
	RUST_LOG=warn cargo tarpaulin --all-features --timeout 120 --out html --output-dir coverage

.PHONY: open-coverage
open-coverage:
	@echo "Opening coverage report..."
	open coverage/tarpaulin-report.html

.PHONY: check-cargo-criterion
check-cargo-criterion:
	@command -v cargo-criterion > /dev/null || cargo install cargo-criterion

.PHONY: bench
bench: check-cargo-criterion
	@echo "Running benchmarks..."
	cargo criterion --output-format=quiet

.PHONY: bench-show
bench-show:
	@echo "Opening benchmark report..."
	open target/criterion/report/index.html

.PHONY: bench-save
bench-save:
	@echo "Saving benchmark baseline..."
	cargo criterion --save-baseline main

.PHONY: bench-compare
bench-compare:
	@echo "Comparing benchmarks against baseline..."
	cargo criterion --baseline main

.PHONY: bench-clean
bench-clean:
	@echo "Cleaning benchmark data..."
	rm -rf target/criterion

# =============================================================================
# Git & Helpers
# =============================================================================

.PHONY: git-log
git-log:
	@if [ "$(CURRENT_BRANCH)" = "HEAD" ]; then \
		echo "You are in a detached HEAD state. Please check out a branch."; \
		exit 1; \
	fi; \
	echo "Showing git log for branch $(CURRENT_BRANCH) against main:"; \
	git log main..$(CURRENT_BRANCH) --pretty=full

.PHONY: check-spanish
check-spanish:
	@echo "Checking for Spanish words in code..."
	@rg -n --pcre2 -e '^\s*(//|///|//!|#|/\*|\*).*?[áéíóúÁÉÍÓÚñÑ¿¡]' \
		--glob '!target/*' \
		--glob '!**/*.png' \
		. && (echo "Spanish comments found"; exit 1) || echo "No Spanish comments found"

.PHONY: tree
tree:
	@echo "Project structure:"
	@tree -I 'target|.git|node_modules|coverage|dist' -L 3

.PHONY: loc
loc:
	@echo "Lines of code:"
	@tokei --exclude target --exclude .git

.PHONY: deps
deps:
	@echo "Dependency tree:"
	cargo tree --depth 1

.PHONY: outdated
outdated:
	@echo "Checking for outdated dependencies..."
	@command -v cargo-outdated > /dev/null || cargo install cargo-outdated
	cargo outdated

.PHONY: audit
audit:
	@echo "Security audit..."
	@command -v cargo-audit > /dev/null || cargo install cargo-audit
	cargo audit

# =============================================================================
# Release
# =============================================================================

.PHONY: version
version:
	@echo "Current version:"
	@grep '^version' Cargo.toml | head -1

.PHONY: tag
tag:
	@echo "Creating git tag..."
	@version=$$(grep '^version' Cargo.toml | head -1 | sed 's/.*"\(.*\)"/\1/'); \
	git tag -a "v$$version" -m "Release v$$version"; \
	echo "Created tag v$$version"

# =============================================================================
# Help
# =============================================================================

.PHONY: help
help:
	@echo ""
	@echo "============================================================"
	@echo "  Hydra AMM - Development Commands"
	@echo "============================================================"
	@echo ""
	@echo "Build:"
	@echo "  make build           Build with all features (debug)"
	@echo "  make build-no-std    Build with no default features"
	@echo "  make build-features  Build all feature combinations"
	@echo "  make release         Build in release mode"
	@echo "  make clean           Clean build artifacts"
	@echo ""
	@echo "Test & Quality:"
	@echo "  make test            Run all tests (all features)"
	@echo "  make test-lib        Run library tests only"
	@echo "  make test-doc        Run documentation tests"
	@echo "  make fmt             Format code"
	@echo "  make fmt-check       Check formatting without applying"
	@echo "  make lint            Run clippy (all features)"
	@echo "  make lint-no-std     Run clippy (no default features)"
	@echo "  make lint-fix        Auto-fix lint issues"
	@echo "  make fix             Auto-fix compiler suggestions"
	@echo "  make check           Run fmt-check + lint + lint-no-std + test"
	@echo "  make pre-push        Run all pre-push checks"
	@echo ""
	@echo "Documentation:"
	@echo "  make doc             Generate documentation"
	@echo "  make doc-open        Generate and open in browser"
	@echo "  make doc-check       Check docs build without warnings"
	@echo ""
	@echo "Packaging & Publishing:"
	@echo "  make publish         Dry-run publish to crates.io"
	@echo "  make package         List package contents"
	@echo ""
	@echo "Coverage & Benchmarks:"
	@echo "  make coverage        Generate XML coverage report"
	@echo "  make coverage-html   Generate HTML coverage report"
	@echo "  make open-coverage   Open HTML coverage report"
	@echo "  make bench           Run benchmarks (criterion)"
	@echo "  make bench-show      Open benchmark report"
	@echo "  make bench-save      Save benchmark baseline"
	@echo "  make bench-compare   Compare against baseline"
	@echo "  make bench-clean     Remove benchmark data"
	@echo ""
	@echo "Git & Helpers:"
	@echo "  make git-log         Show commits on branch vs main"
	@echo "  make check-spanish   Check for Spanish in comments"
	@echo "  make tree            Show project structure"
	@echo "  make loc             Count lines of code"
	@echo "  make deps            Show dependency tree (depth 1)"
	@echo "  make outdated        Check for outdated dependencies"
	@echo "  make audit           Run security audit"
	@echo ""
	@echo "Release:"
	@echo "  make version         Show current version"
	@echo "  make tag             Create git tag from Cargo.toml version"
	@echo ""
