#pragma once

namespace slang {

class Token;

// maintains a sliding window of lexed tokens
// sometimes parsing needs to lookahead and roll back to a reset point

template<Token* (Lexer::*next)()>
class TokenWindow {
public:
    TokenWindow(Lexer& source) : source(source) {
        capacity = 32;
        buffer = new Token*[capacity];
    }

    ~TokenWindow() {
        delete[] buffer;
    }

    Token* peek(int offset) {
        while (currentOffset + offset >= count)
            addNew();
        return buffer[currentOffset + offset];
    }

    Token* peek() {
        if (!currentToken) {
            if (currentOffset >= count)
                addNew();
            currentToken = buffer[currentOffset];
        }
        return currentToken;
    }

    bool peek(TokenKind kind) {
        return peek()->kind == kind;
    }

    Token* consume() {
        auto result = peek();
        moveToNext();
        return result;
    }

    Token* consumeIf(TokenKind kind) {
        auto result = peek();
        if (result->kind != kind)
            return nullptr;

        moveToNext();
        return result;
    }

    Token* expect(TokenKind kind) {
        auto result = peek();
        if (result->kind != kind)
            return Token::missing(source.getPreprocessor().getAllocator(), kind);

        moveToNext();
        return result;
    }

private:
    Lexer& source;
    Token** buffer = nullptr;
    Token* currentToken = nullptr;
    int currentOffset = 0;
    int count = 0;
    int capacity;

    void addNew() {
        if (count >= capacity) {
            // shift tokens to the left if we are too far to the right
            if (currentOffset > (capacity >> 1)) {
                int shift = count - currentOffset;
                if (shift > 0)
                    memmove(buffer, buffer + currentOffset, shift);

                count -= currentOffset;
                currentOffset = 0;
            }
            else {
                Token** newBuffer = new Token*[capacity * 2];
                memcpy(newBuffer, buffer, count);

                delete[] buffer;
                buffer = newBuffer;
            }
        }
        buffer[count] = (source.*next)();
        count++;
    }

    void moveToNext() {
        currentToken = nullptr;
        currentOffset++;
    }
};

}