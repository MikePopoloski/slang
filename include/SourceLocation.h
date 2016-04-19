#pragma once

namespace slang {

// Represents a location in source code. The SourceManager can decode this into
// file, line, and column information.

class SourceLocation {
public:
	SourceLocation() : id(0) {}

	bool isValid() const { return id != 0; }

	bool operator ==(const SourceLocation& rhs) {
		return id == rhs.id;
	}

	bool operator !=(const SourceLocation& rhs) {
		return id != rhs.id;
	}

	bool operator <(const SourceLocation& rhs) {
		return id < rhs.id;
	}

private:
	uint32_t id;
};

}