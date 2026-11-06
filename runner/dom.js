// dom.js — the smallest `document` that lets an Elm program (`main = Html.text ...`, or a
// Browser.element whose view changes) run on node. The tests print with Debug.log; the rendered
// view is built and patched, and otherwise ignored.
// install() defines the global `document` (it must run before the program is required:
// elm/virtual-dom reads `document` once, at load) and returns the node to mount on.
//
// Where elm/virtual-dom can hit a browser error, the stub throws as a browser does, so that a
// program that would crash in a browser crashes here too:
//   - the node methods reject an argument that is not a node, or a reference node that is not a
//     child;
//   - a document fragment inserts its children, not itself;
//   - `type` is read-only on <textarea> and <select>, so assigning it throws (Elm's code is strict);
//   - setAttribute rejects a name that is not a valid attribute name (the DOM standard's rule:
//     not empty, no whitespace, NUL, `/`, `=` or `>`).
'use strict';

function notANode(method, arg) {
    return new TypeError("Failed to execute '" + method + "' on 'Node': parameter " + arg + " is not of type 'Node'.");
}

function notFound(method) {
    return new DOMException("Failed to execute '" + method + "' on 'Node': The node is not a child of this node.",
        'NotFoundError');
}

function checkAttributeName(method, name) {
    if (name === '' || /[\t\n\f\r \0\/=>]/.test(name)) {
        throw new DOMException("Failed to execute '" + method + "' on 'Element': '" + name +
            "' is not a valid attribute name.", 'InvalidCharacterError');
    }
}

class Node {
    constructor(nodeName) {
        this.nodeName = nodeName;
        this.childNodes = [];
        this.parentNode = null;
        this.attributes = {};
        this.style = {};
    }
    // Inserts child (or a fragment's children) before index i of childNodes.
    insertAt(child, i) {
        const kids = child.nodeName === '#document-fragment' ? child.childNodes.splice(0) : [child];
        for (const kid of kids) {
            if (kid.parentNode) {
                const j = kid.parentNode.childNodes.indexOf(kid);
                if (kid.parentNode === this && j < i) i--;
                kid.parentNode.childNodes.splice(j, 1);
            }
            kid.parentNode = this;
            this.childNodes.splice(i++, 0, kid);
        }
        return child;
    }
    appendChild(child) {
        if (!(child instanceof Node)) throw notANode('appendChild', 1);
        return this.insertAt(child, this.childNodes.length);
    }
    insertBefore(child, ref) {
        if (!(child instanceof Node)) throw notANode('insertBefore', 1);
        if (ref === null || ref === undefined) return this.appendChild(child);
        if (!(ref instanceof Node)) throw notANode('insertBefore', 2);
        if (ref.parentNode !== this) throw notFound('insertBefore');
        return this.insertAt(child, this.childNodes.indexOf(ref));
    }
    removeChild(child) {
        if (!(child instanceof Node)) throw notANode('removeChild', 1);
        if (child.parentNode !== this) throw notFound('removeChild');
        this.childNodes.splice(this.childNodes.indexOf(child), 1);
        child.parentNode = null;
        return child;
    }
    replaceChild(child, old) {
        if (!(child instanceof Node)) throw notANode('replaceChild', 1);
        if (!(old instanceof Node)) throw notANode('replaceChild', 2);
        if (old.parentNode !== this) throw notFound('replaceChild');
        if (child !== old) {
            this.insertBefore(child, old);
            this.removeChild(old);
        }
        return old;
    }
    get firstChild() { return this.childNodes[0] || null; }
    get lastChild() { return this.childNodes[this.childNodes.length - 1] || null; }
    setAttribute(key, value) { checkAttributeName('setAttribute', key); this.attributes[key] = String(value); }
    setAttributeNS(ns, key, value) {
        checkAttributeName('setAttributeNS', key.slice(key.indexOf(':') + 1));
        this.attributes[key] = String(value);
    }
    removeAttribute(key) { delete this.attributes[key]; }
    removeAttributeNS(ns, key) { delete this.attributes[key]; }
    getAttribute(key) { return key in this.attributes ? this.attributes[key] : null; }
    addEventListener() {}
    removeEventListener() {}
}

class Text extends Node {
    constructor(data) {
        super('#text');
        this.data = String(data);
    }
    get length() { return this.data.length; }
    replaceData(offset, count, data) {
        this.data = this.data.slice(0, offset) + data + this.data.slice(offset + count);
    }
}

// The element types whose `type` property has only a getter.
const readOnlyType = { TEXTAREA: 'textarea', SELECT: 'select-one' };

function install() {
    const document = {
        createElement: (tag) => {
            const node = new Node(tag.toUpperCase());
            if (node.nodeName in readOnlyType) {
                const type = readOnlyType[node.nodeName];
                Object.defineProperty(node, 'type', { get: () => type, enumerable: true });
            }
            return node;
        },
        createElementNS: (ns, tag) => new Node(tag),
        createTextNode: (text) => new Text(text),
        createDocumentFragment: () => new Node('#document-fragment'),
    };
    document.body = document.createElement('body');
    global.document = document;
    return document.body.appendChild(document.createElement('div'));
}

module.exports = { install };
