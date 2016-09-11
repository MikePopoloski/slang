#pragma once

namespace slang {

class BoundNode {
};

class BoundExpression : public BoundNode {
};

class BoundParameterDeclaration : public BoundNode {
public:
    uint64_t value;
};

}