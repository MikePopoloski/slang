#pragma once

namespace slang {

template<typename T>
class HandleBase {
public:
    bool valid() const { return id != 0; }
    bool operator==(const T& rhs) const { return id == rhs.id; }
    bool operator!=(const T& rhs) const { return !(*this == rhs); }

    explicit operator bool() const {
        return valid();
    }
    uint32_t id = 0;

protected:
    static T get(uint32_t value) {
        T result;
        result.id = value;
        return result;
    }
    uint32_t getValue() const { return id; }

private:
};

}