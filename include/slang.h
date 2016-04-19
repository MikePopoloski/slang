#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <deque>
#include <unordered_map>
#include <filesystem>

#include "Debug.h"
#include "Hash.h"
#include "Handle.h"
#include "BumpAllocator.h"
#include "ArrayRef.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "StringRef.h"
#include "StringTable.h"
#include "SourceManager.h"
#include "BitVector.h"
#include "Diagnostics.h"
#include "Trivia.h"
#include "Token.h"
#include "Lexer.h"
#include "Preprocessor.h"
#include "AllSyntax.h"
#include "Parser.h"