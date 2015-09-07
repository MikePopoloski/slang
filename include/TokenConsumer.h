#pragma once

namespace slang {

template<typename T, int WindowSize>
class TokenConsumer {
    static_assert(WindowSize > 0 && (WindowSize & (WindowSize - 1)) == 0, "WindowSize must be a power of two.");

protected:
    void setSource(T* source) { tokenSource = source; }

    Token* peek() {
        ensureSlot(0);
        return window[readPtr];
    }

    Token* peek(int offset) {
        ensureSlot(offset);
        return window[(readPtr + offset) & (WindowSize - 1)];
    }

    Token* consume() {
        Token* token = peek();
        readPtr = (readPtr + 1) & (WindowSize - 1);
        count--;
        ASSERT(count >= 0);
        return token;
    }

    Token* consume(TokenKind kind) {
        if (peek()->kind == kind)
            return consume();
        return nullptr;
    }

private:
    Token* window[WindowSize];
    T* tokenSource = nullptr;
    int readPtr = 0;
    int writePtr = 0;
    int count = 0;

    void ensureSlot(int offset) {
        int need = offset - count + 1;
        while (need-- > 0) {
            window[writePtr] = tokenSource->lex();
            writePtr = (writePtr + 1) & (WindowSize - 1);
            count++;
            ASSERT(count < WindowSize);
        }
    }
};

}