#pragma once

#include <unordered_map>

#include "StringRef.h"

namespace slang {

class Symbol;

// Maintains context (like in a specific scope) and knows about parent
// contexts so that symbol lookup can be performed.
class Scope {
public:
	void add(const Symbol* symbol);

	template<typename TContainer>
	void addRange(const TContainer& container) {
		for (const auto& symbol : container)
			add(symbol);
	}

	const Symbol* lookup(StringRef name);

private:
	std::unordered_map<StringRef, const Symbol*> table;
};

}