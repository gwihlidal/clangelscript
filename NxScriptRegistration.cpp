// THIS FILE WAS AUTOMATICALLY GENERATED BY CLANGELSCRIPT. DO NOT MODIFY.

#include <angelscript.h>
#include <assert.h>

#include "./textcomponent.h"

#define RegisterVerifyAPI(EXPRESSION) assert((EXPRESSION) >= asSUCCESS)

template<class A, class B>
B* refCast(A* a)
{
    if(!a) return NULL;

    B* b = dynamic_cast<B*>(a);
    if (b != NULL)
    {
        b->AddRef();
    }
    return b;
}

template<class A, class B>
B* refCast_nocount(A* a)
{
    if( !a ) return NULL;
    return dynamic_cast<B*>(a);
}

void TextComponent_TextComponent_generic(asIScriptGeneric *gen)
{
	new(gen->GetObject()) TextComponent();
}


void registerScripting(asIScriptEngine* engine)
{
    // Object Types
    RegisterVerifyAPI(engine->RegisterObjectType("TestStruct", sizeof(TestStruct), asOBJ_VALUE|asOBJ_POD|asOBJ_APP_CLASS_ALLINTS|asOBJ_APP_CLASS));
    RegisterVerifyAPI(engine->RegisterObjectType("TextComponent", sizeof(TextComponent), asOBJ_VALUE|asOBJ_APP_CLASS_CONSTRUCTOR|asOBJ_POD|asOBJ_APP_CLASS_ALLINTS|asOBJ_APP_CLASS));

    // Type Definitions, Defines, Enums
    RegisterVerifyAPI(engine->RegisterEnum("HASH_DEFINES"));

    // Functions
    RegisterVerifyAPI(engine->RegisterGlobalFunction("void testFunc()", asFUNCTIONPR(testFunc, (), void), asCALL_CDECL));

    // Behaviours
    RegisterVerifyAPI(engine->RegisterObjectBehaviour("TextComponent", asBEHAVE_CONSTRUCT, "void f()", asFUNCTION(TextComponent_TextComponent_generic), asCALL_GENERIC));

    // Object Methods
    RegisterVerifyAPI(engine->RegisterObjectMethod("TextComponent", "std::__1::string text() const", asMETHODPR(TextComponent, text, () const, std::__1::string), asCALL_THISCALL));
    RegisterVerifyAPI(engine->RegisterObjectMethod("TextComponent", "void setText(const std::__1::string&in)", asMETHODPR(TextComponent, setText, (const std::__1::string&), void), asCALL_THISCALL));
    RegisterVerifyAPI(engine->RegisterObjectMethod("TextComponent", "int blah() const", asMETHODPR(TextComponent, blah, () const, int), asCALL_THISCALL));
    RegisterVerifyAPI(engine->RegisterObjectMethod("TextComponent", "void setBlah(int)", asMETHODPR(TextComponent, setBlah, (int), void), asCALL_THISCALL));
    RegisterVerifyAPI(engine->RegisterObjectMethod("TextComponent", "void superSecretFunction()", asMETHODPR(TextComponent, superSecretFunction, (), void), asCALL_THISCALL));

    // Object Fields
    RegisterVerifyAPI(engine->RegisterObjectProperty("TestStruct", "int a", asOFFSET(TestStruct,a)));
    RegisterVerifyAPI(engine->RegisterObjectProperty("TestStruct", "char_s b", asOFFSET(TestStruct,b)));
    RegisterVerifyAPI(engine->RegisterObjectProperty("TestStruct", "double c", asOFFSET(TestStruct,c)));
    RegisterVerifyAPI(engine->RegisterObjectProperty("TestStruct", "float d", asOFFSET(TestStruct,d)));
    RegisterVerifyAPI(engine->RegisterObjectProperty("TextComponent", "unsigned int testVar", asOFFSET(TextComponent,testVar)));
    RegisterVerifyAPI(engine->RegisterObjectProperty("TextComponent", "TestStruct testStruct", asOFFSET(TextComponent,testStruct)));
}