#!/bin/bash
#
# run-tlc.sh - Run TLC model checker locally
#
# Usage:
#   ./tlaplus/scripts/run-tlc.sh [spec-name]
#
# Examples:
#   ./tlaplus/scripts/run-tlc.sh           # Run Inventory spec
#   ./tlaplus/scripts/run-tlc.sh Inventory # Same as above
#
# Requirements:
#   - Java 11+ installed
#   - tla2tools.jar downloaded (script will download if missing)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPECS_DIR="$SCRIPT_DIR/../specs"
TOOLS_DIR="$SCRIPT_DIR/../tools"
TLA_VERSION="1.8.0"
TLA_JAR="$TOOLS_DIR/tla2tools.jar"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default spec
SPEC_NAME="${1:-Inventory}"

echo -e "${BLUE}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║           Noema TLA+ Model Checker                         ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Check Java
if ! command -v java &> /dev/null; then
    echo -e "${RED}Error: Java not found. Please install Java 11+${NC}"
    exit 1
fi

JAVA_VERSION=$(java -version 2>&1 | head -1 | cut -d'"' -f2 | cut -d'.' -f1)
echo -e "${GREEN}✓${NC} Java version: $JAVA_VERSION"

# Download TLA+ tools if needed
if [ ! -f "$TLA_JAR" ]; then
    echo -e "${YELLOW}Downloading TLA+ tools v$TLA_VERSION...${NC}"
    mkdir -p "$TOOLS_DIR"
    curl -L -o "$TLA_JAR" \
        "https://github.com/tlaplus/tlaplus/releases/download/v$TLA_VERSION/tla2tools.jar"
    echo -e "${GREEN}✓${NC} Downloaded tla2tools.jar"
fi

# Check spec files exist
SPEC_FILE="$SPECS_DIR/$SPEC_NAME.tla"
CFG_FILE="$SPECS_DIR/$SPEC_NAME.cfg"

if [ ! -f "$SPEC_FILE" ]; then
    echo -e "${RED}Error: Spec file not found: $SPEC_FILE${NC}"
    exit 1
fi

if [ ! -f "$CFG_FILE" ]; then
    echo -e "${RED}Error: Config file not found: $CFG_FILE${NC}"
    exit 1
fi

echo -e "${GREEN}✓${NC} Spec: $SPEC_NAME.tla"
echo -e "${GREEN}✓${NC} Config: $SPEC_NAME.cfg"
echo ""

# Run TLC
echo -e "${BLUE}Running TLC model checker...${NC}"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

cd "$SPECS_DIR"

START_TIME=$(date +%s)

java -XX:+UseParallelGC \
     -Xmx4g \
     -jar "$TLA_JAR" \
     -config "$SPEC_NAME.cfg" \
     -workers auto \
     -deadlock \
     "$SPEC_NAME.tla" 2>&1 | tee tlc-output.txt

TLC_EXIT_CODE=${PIPESTATUS[0]}

END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Report results
if [ $TLC_EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║           TLA+ Verification PASSED ✓                       ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    echo "Duration: ${DURATION}s"
    
    # Extract statistics
    if grep -q "states generated" tlc-output.txt; then
        echo ""
        grep "states generated" tlc-output.txt | tail -1
    fi
else
    echo -e "${RED}╔════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${RED}║           TLA+ Verification FAILED ✗                       ║${NC}"
    echo -e "${RED}╚════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    
    # Extract error info
    if grep -q "Invariant.*violated" tlc-output.txt; then
        echo -e "${RED}Invariant Violation:${NC}"
        grep "Invariant.*violated" tlc-output.txt
        echo ""
    fi
    
    # Show counterexample
    if grep -q "State 1:" tlc-output.txt; then
        echo -e "${YELLOW}Counterexample Trace:${NC}"
        sed -n '/State 1:/,/^$/p' tlc-output.txt
    fi
    
    echo ""
    echo -e "${YELLOW}Suggested Actions:${NC}"
    echo "1. Review the counterexample trace"
    echo "2. Check if the invariant is too strict"
    echo "3. Add guards in the Handler (Cognition) layer"
fi

echo ""
echo "Full output: $SPECS_DIR/tlc-output.txt"

exit $TLC_EXIT_CODE
