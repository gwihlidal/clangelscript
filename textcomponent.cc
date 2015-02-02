#include <iostream>

#include "textcomponent.h"

TextComponent::TextComponent()
    : m_text("")
{
}

string TextComponent::text() const
{
    return m_text;
}

void TextComponent::setText(string const& value)
{
    m_text = value;
}

int TextComponent::blah() const
{
    return m_blah;
}

void TextComponent::setBlah(int val)
{
    m_blah = val;
}

void TextComponent::superSecretFunction()
{
    std::cout << "HOW DID YOU FIND ME" << std::endl;
}

