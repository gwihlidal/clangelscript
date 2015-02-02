#pragma once 

#include <string>

#ifdef __CLANGELSCRIPT__
#define HIDDEN __attribute__((annotate("hidden")))
#else
#define HIDDEN
#endif

void testFunc() { int blah; blah += 4; }

using namespace std;

struct TestStruct
{
    int a;
    char b;
    double c;
    float d;
};

class TextComponent  
{
public:
    TextComponent();

    string text() const;
    void setText(const string& value);

    int blah() const;
    void setBlah(int val);

    HIDDEN void superSecretFunction();

    unsigned int testVar;

    TestStruct testStruct;

private:
    string m_text;
    int m_blah;
};
