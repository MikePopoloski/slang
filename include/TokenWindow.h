#pragma once

namespace slang {

class Token;

// Internal helper class that maintains a sliding window of tokens.
// Sometimes parsing needs to lookahead and roll back to a reset point.
//
// TSource must expose getAllocator(), getDiagnostics(), and next() functions.

template<typename TSource>
class TokenWindow {
public:
	explicit TokenWindow(TSource& source) :
		tokenSource(source)
	{
		capacity = 32;
		windowBuffer = new Token*[capacity];
	}

    ~TokenWindow() {
        delete[] windowBuffer;
    }

    TokenWindow(const TokenWindow&) = delete;
    TokenWindow& operator=(const TokenWindow&) = delete;

    Token* peek(int offset) {
        while (currentOffset + offset >= count)
            addNew();
        return windowBuffer[currentOffset + offset];
    }

    Token* peek() {
        if (!currentToken) {
            if (currentOffset >= count)
                addNew();
            currentToken = windowBuffer[currentOffset];
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
        if (result->kind != kind) {
            // report an error here for the missing token
            // TODO: location info
			tokenSource.getDiagnostics().add(SyntaxError(DiagCode::SyntaxError, 0, 0));
            return Token::missing(tokenSource.getAllocator(), kind);
        }

        moveToNext();
        return result;
    }

private:
	TSource& tokenSource;
    Token** windowBuffer = nullptr;
    Token* currentToken = nullptr;
    int currentOffset = 0;
    int count = 0;
    int capacity = 0;

    void addNew() {
        if (count >= capacity) {
            // shift tokens to the left if we are too far to the right
            if (currentOffset > (capacity >> 1)) {
                int shift = count - currentOffset;
                if (shift > 0)
                    memmove(windowBuffer, windowBuffer + currentOffset, shift * sizeof(Token*));

                count -= currentOffset;
                currentOffset = 0;
            }
            else {
                Token** newBuffer = new Token*[capacity * 2];
                memcpy(newBuffer, windowBuffer, count * sizeof(Token*));

                delete[] windowBuffer;
				windowBuffer = newBuffer;
            }
        }
		windowBuffer[count] = tokenSource.next();
        count++;
    }

    void moveToNext() {
        currentToken = nullptr;
        currentOffset++;
    }
};

}