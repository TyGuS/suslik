import $ from 'jquery';
import Vue from 'vue/dist/vue';
import './proof-trace.css';



class ProofTrace {

    data: Data
    root: Data.NodeEntry

    nodeIndex: {
        byId: JSONMap<Data.NodeId, Data.NodeEntry>
        childrenById: JSONMap<Data.NodeId, Data.NodeEntry[]>
    }

    view: Vue

    constructor(data: ProofTrace.Data) {
        this.data = data;
        this.root = this.data.nodes[0];

        this.createIndex();
        this.createView();
    }

    createIndex() {
        this.nodeIndex = {byId: new JSONMap(), childrenById: new JSONMap()};
        for (let node of this.data.nodes)
            this.nodeIndex.byId.set(node.id, node);

        var m = this.nodeIndex.childrenById;
        for (let node of this.data.nodes) {
            if (node.id.length > 1) {
                var parent = node.id.slice(2);  // @todo AndNode
                m.set(parent, (m.get(parent) || []).concat([node]));
            }
        }
    }

    children(node: Data.NodeEntry) {
        return this.nodeIndex.childrenById.get(node.id) || [];
    }

    createView() {
        this.view = new (Vue.component('proof-trace'))();
        this.view.root = {
            value: this.root, children: undefined, expanded: true
        };
        this.expandNode(this.view.root);
        this.expandNode(this.view.root.children[0]);
        this.view.$mount();

        this.view.$on('action', (ev: View.ActionEvent) => this.viewAction(ev))
    }

    viewAction(ev: View.ActionEvent) {
        switch (ev.type) {
        case 'expand':
            this.expandNode(ev.target); break;
        }
    }

    expandNode(nodeView: View.Node) {
        nodeView.children = this.children(nodeView.value)
            .map(value => ({value, children: undefined, expanded: false}));
    }

}


namespace ProofTrace {

    export type Data = {
        nodes: Data.NodeEntry[]
    };

    export namespace Data {

        export type NodeEntry = {
            id: NodeId
            pp: string
            goal: GoalEntry 
        };

        export type NodeId = number[];

        export type GoalEntry = {
            pre: string, post: string, sketch: string,
            programVars:  [string, string][]
            existentials: [string, string][]
        };

        export type Environment = Map<string, {type: string, of: string}>;

        export function parse(traceText: string): Data {
            var nodes = traceText.split('\n\n').filter(x => x).map(ln =>
                            JSON.parse(ln));
            return {nodes};
        };

        export function envOfGoal(goal: GoalEntry) {
            var d: Environment = new Map;
            for (let [type, name] of goal.programVars)
                d.set(name, {type, of: 'programVars'});
            for (let [type, name] of goal.existentials)
                d.set(name, {type, of: 'existentials'});
            return d;
        }

    }

    // =========
    // View Part
    // =========
    export namespace View {

        export type Node = {
            value: Data.NodeEntry,
            children: Node[],
            expanded: boolean;
        };

        export type ActionEvent = {
            type: "expand",
            target: Node
        };

        const OPERATORS = new Map([
            [':->', {pp: "↦"}], ['==', {}], ['**', {pp: '∗'}], ['&&', {pp: "∧"}],
            ['=i', {pp: "=ᵢ"}], ['++', {pp: '∪'}]]);

        export function tokenize(pp: string, env: Data.Environment) {
            return pp.split(/(\s+|[(){},])/).map(s => {
                var v = env.get(s), op = OPERATORS.get(s);
                if (v)
                    return {kind: 'var', text: s, ...v};
                else if (op)
                    return {kind: 'op', text: s, ...op};
                else if (s.match(/^\s+$/))
                    return {kind: 'whitespace', text: s};
                else if (s.match(/^[(){}]$/))
                    return {kind: 'brace', text: s};
                else if (s != '')
                    return {kind: 'unknown', text: s};
            })
            .filter(x => x);
        }
        
    }

}

import Data = ProofTrace.Data;
import View = ProofTrace.View;



abstract class KeyedMap<K, V, K0> {
    _map: Map<K0, V> = new Map();
    abstract key(k: K): K0;
    set(k: K, v: V) {
        this._map.set(this.key(k), v);
    }
    get(k: K) {
        return this._map.get(this.key(k));
    }
}

class JSONMap<K, V> extends KeyedMap<K, V, string> {
    key(k: K) { return JSON.stringify(k); }
}


Vue.component('proof-trace', {
    props: ['root'],
    template: `
        <div class="proof-trace">
            <template v-if="root">
                <proof-trace-node :value="root.value" @action="nodeAction"/>
                <div class="subtrees" ref="subtrees" v-if="root.expanded">
                    <template v-for="child in root.children">
                        <proof-trace :root="child" @action="action"/>
                    </template>
                </div>
            </template>
        </div>`,
    mounted() {
        this.$watch('root.expanded', () => {
            requestAnimationFrame(() => {
                if (this.$refs.subtrees)
                    this.$refs.subtrees.scrollIntoView({block: 'end', behavior: 'smooth'});
                else
                    window.scrollBy(0, -1);
            });
        });
    },
    methods: {
        action(ev) { this.$emit('action', ev); },
        nodeAction(ev) {
            if (ev.type == 'expand' && ev.target == this.root.value)
                this.root.expanded = !this.root.expanded;
            this.action({...ev, target: this.root});
        }
    }
});

Vue.component('proof-trace-node', {
    props: ['value'],
    data: () => ({_anchor: false}),
    template: `
        <div class="proof-trace-node" @click="expand" @mouseenter="showId"
                @mousedown="clickStart" @click.capture="clickCapture"">
            <div @mousedown="stopDbl" class="title">{{value.pp}}</div>
            <proof-trace-goal @click.native.stop="action" :value="value.goal"/>
        </div>`,
    methods: {
        action(ev) { this.$emit('action', ev); },
        expand() { this.action({type: 'expand', target: this.value}); },
        showId() { $('#hint').text(JSON.stringify(this.value.id)); },
        stopDbl(ev) { if (ev.detail > 1) ev.preventDefault(); },
        // boilerplate to prevent click after selection
        clickStart(ev) { this.$data._anchor = {x: ev.pageX, y: ev.pageY}; },
        clickCapture(ev) { 
            var a = this.$data._anchor;
            if (a && (ev.pageX - a.x > 3 || ev.pageY - a.y > 3))
                ev.stopPropagation();
        }
    }
});

Vue.component('proof-trace-goal', {
    props: ['value'],
    template: `
        <div class="proof-trace-goal">
            <proof-trace-vars :value="value.programVars"  class="proof-trace-program-vars"/>
            <proof-trace-vars :value="value.existentials" class="proof-trace-existentials"/>
            <proof-trace-formula class="proof-trace-pre" :pp="value.pre" :env="env"/>
            <div class="proof-trace-sketch">{{value.sketch}} </div>
            <proof-trace-formula class="proof-trace-post" :pp="value.post" :env="env"/>
        </div>`,
    computed: {
        env() { return Data.envOfGoal(this.value); }
    }
});

Vue.component('proof-trace-vars', {
    props: ['value'],
    template: `
        <div class="proof-trace-vars">
            <template v-for="v in value">
                <span>
                    <span class="type">{{v[0]}}</span>
                    <span class="name">{{v[1]}}</span>
                </span>
            </template>
        </div>`
});

Vue.component('proof-trace-formula', {
    props: ['pp', 'env', 'css-class'],
    template: `
        <div class="proof-trace-formula">
            <template v-for="token in tokenize(pp, env)">
                <span :class="token.kind" 
                    :data-of="token.of">{{token.pp || token.text}}</span>
            </template>
        </div>`,
    methods: {
        tokenize: View.tokenize
    }
})



export { ProofTrace }
