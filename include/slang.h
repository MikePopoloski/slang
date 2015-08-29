#pragma once

#include <vector>
#include <string>
#include <cstdint>
#include <memory>
#include <algorithm>
#include <type_traits>

#define ASSERT(x) do { if (!(x)) __debugbreak(); } while(0) 

#include "Allocator.h"
#include "ArrayRef.h"
#include "StringRef.h"
#include "Buffer.h"
#include "BitVector.h"
#include "Diagnostics.h"
#include "Trivia.h"
#include "Token.h"
#include "Preprocessor.h"
#include "Lexer.h"
#include "SyntaxFacts.h"