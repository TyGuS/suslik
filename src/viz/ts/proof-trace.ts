import $ from 'jquery';
import Vue from 'vue/dist/vue';
import './proof-trace.css';



class ProofTrace {

    data: Data
    root: Data.NodeEntry

    nodeIndex: {
        byId: JSONMap<Data.NodeId, Data.NodeEntry>
        childrenById: JSONMap<Data.NodeId, Data.NodeEntry[]>
        statusById: JSONMap<Data.NodeId, Data.StatusEntry>
    }

    view: Vue

    constructor(data: ProofTrace.Data) {
        this.data = data;
        this.root = this.data.nodes[0];

        this.createIndex();
        this.createView();
    }

    createIndex() {
        this.nodeIndex = {
            byId: new JSONMap(),
            childrenById: new JSONMap(), statusById: new JSONMap()
        };
        // Build byId
        for (let node of this.data.nodes)
            this.nodeIndex.byId.set(node.id, node);

        // Build childrenById
        var m = this.nodeIndex.childrenById;
        for (let node of this.data.nodes) {
            if (node.id.length >= 1) {
                var parent = node.id.slice(1);
                m.set(parent, (m.get(parent) || []).concat([node]));
            }
        }

        // Build statusById
        for (let entry of this.data.statuses) {
            var id = entry.at;
            this.nodeIndex.statusById.set(id, entry);
        }

        for (let node of this.data.nodes.sort((a, b) => b.id.length - a.id.length)) {
            if (!this.nodeIndex.statusById.get(node.id)) {
                var children = (this.nodeIndex.childrenById.get(node.id) || [])
                                .map(c => this.nodeIndex.statusById.get(c.id));
                if (children.length) {
                    switch (node.tag) {
                    case Data.NodeType.OrNode:
                        if (children.some(x => x && x.status.tag === 'Succeeded'))
                            this.nodeIndex.statusById.set(node.id, {at: node.id, status: {tag: 'Succeeded', from: '*'}});
                        break;
                    case Data.NodeType.AndNode:
                        if (children.length == node.nChildren &&
                            children.every(x => x && x.status.tag === 'Succeeded'))
                            this.nodeIndex.statusById.set(node.id, {at: node.id, status: {tag: 'Succeeded', from: '*'}});
                        break;
                    }
                }
            }
        }
    }

    children(node: Data.NodeEntry) {
        function lex2(a1: number[], a2: number[]) {
            let n = Math.min(2, a1.length, a2.length);
            for (let i = n - 1; i >= 0; i--) {
                if      (a1[i] < a2[i]) return -1;
                else if (a1[i] > a2[i]) return 1;
            }
            return 0;
        }
        function byId2(u1: Data.NodeEntry, u2: Data.NodeEntry) {
            return lex2(u1.id, u2.id);
        }
        return (this.nodeIndex.childrenById.get(node.id) || [])
            .sort(byId2); // modifies the list but that's ok
    }

    createView() {
        this.view = new (Vue.component('proof-trace'))();
        this.view.root = this.createNode(this.root);
        this.expandNode(this.view.root);
        this.expandNode(this.view.root.children[0]);
        //this.expandAll(this.view.root);
        this.view.$mount();

        this.view.$on('action', (ev: View.ActionEvent) => this.viewAction(ev))
    }

    getStatus(node: Data.NodeEntry): Data.GoalStatusEntry { 
        var entry = this.nodeIndex.statusById.get(node.id);
        return entry && entry.status;
    }

    createNode(node: Data.NodeEntry): View.Node {
        return {value: node, children: undefined, focus: false, expanded: false,
                status: this.getStatus(node)};
    }

    expandNode(nodeView: View.Node, focus: boolean = false) {
        nodeView.focus = focus;
        nodeView.expanded = true;
        nodeView.children = this.children(nodeView.value)
            .map(node => this.createNode(node));
    }

    expandOrNode(nodeView: View.Node, focus: boolean = false) {
        this.expandNode(nodeView, focus);
        for (let c of nodeView.children) {
            if (c.value.tag == Data.NodeType.AndNode) {
                this.expandOrNode(c, focus);
            }
        }
    }

    expandAll(nodeView: View.Node = this.view.root) {
        this.expandNode(nodeView);
        for (let c of nodeView.children)
            this.expandAll(c);
    }

    viewAction(ev: View.ActionEvent) {
        switch (ev.type) {
        case 'expand':
            this.expandOrNode(ev.target, true); break;
        case 'expandAll':
            this.expandAll(ev.target); break;
        }
    }

}


namespace ProofTrace {

    export type Data = {
        nodes: Data.NodeEntry[],
        statuses: Data.StatusEntry[]
    };

    export namespace Data {

        export type NodeEntry = {
            id: NodeId
            tag: NodeType
            pp: string
            goal: GoalEntry
            nChildren: number
        };

        export type NodeId = number[];

        export enum NodeType { AndNode = 'AndNode', OrNode = 'OrNode' };

        export type GoalEntry = {
            pre: string, post: string, sketch: string,
            programVars:  [string, string][]
            existentials: [string, string][]
            ghosts:       [string, string][]
        };

        export type Environment = Map<string, {type: string, of: string}>;

        export type StatusEntry = {
            at: NodeId
            status: GoalStatusEntry
        };

        export type GoalStatusEntry = {tag: "Succeeded" | "Failed", from?: string};

        export function parse(traceText: string): Data {
            var entries = traceText.split('\n\n').filter(x => x).map(ln =>
                            JSON.parse(ln));
            var nodes = [], statuses = [];
            for (let e of entries) {
                if (e.tag) nodes.push(e);
                else if (e.status) statuses.push(e);
            }
            return {nodes, statuses};
        }

        export function envOfGoal(goal: GoalEntry) {
            var d: Environment = new Map;
            function intro(vs: [string, string][], of: string) {
                for (let [type, name] of vs) d.set(name, {type, of});
            }
            intro(goal.programVars, 'programVars');
            intro(goal.existentials, 'existentials');
            intro(goal.ghosts, 'ghosts');
            return d;
        }

    }

    // =========
    // View Part
    // =========
    export namespace View {

        export type Node = {
            value: Data.NodeEntry
            children: Node[]
            status: Data.GoalStatusEntry
            focus: boolean
            expanded: boolean
        };

        export type ActionEvent = {
            type: "expand" | "collapse" | "expandAll",
            target: Node
        };

        const OPERATORS = new Map([
            [':->', {pp: "↦"}], ['==', {pp: "="}], ['**', {pp: '∗'}], ['&&', {pp: "∧"}],
            ['not', {pp: "¬"}], ['=i', {pp: "=ᵢ"}], ['++', {pp: '∪'}]]);

        export function tokenize(pp: string, env: Data.Environment) {
            return pp.split(/(\s+|[(){}[\],])/).map(s => {
                var v = env.get(s), op = OPERATORS.get(s), mo: RegExpMatchArray;
                if (v)
                    return {kind: 'var', text: s, ...v};
                else if (op)
                    return {kind: 'op', text: s, ...op};
                else if (s.match(/^\s+$/))
                    return {kind: 'whitespace', text: s};
                else if (s.match(/^[(){}[\]]$/))
                    return {kind: 'brace', text: s};
                else if (mo = s.match(/^<(\w+)>$/)) {
                    return {kind: 'cardinality', text: mo[1]};
                }
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
                <proof-trace-node :value="root.value" :status="root.status"
                                  @action="nodeAction"/>
                <div class="proof-trace-expand-all" :class="{root: root.value.id.length == 0}">
                    <span @click="expandAll">++</span>
                </div>
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
                if (this.root.focus && this.$refs.subtrees)
                    this.focusElement(this.$refs.subtrees);
            });
        });
    },
    methods: {
        action(ev) { this.$emit('action', ev); },
        nodeAction(ev) {
            if (ev.type == 'expand/collapse') {
                this.root.expanded = !this.root.expanded;
                ev.type = this.root.expanded ? 'expand' : 'collapse';
            }
            this.action({...ev, target: this.root});
        },
        expandAll() { this.action({type: 'expandAll', target: this.root})},
        focusElement(el: HTMLElement) {
            var box = el.getBoundingClientRect(), clrse = 50,
                viewport = (<any>window).visualViewport,
                v = (box.bottom + clrse) - viewport.height,
                hl = box.left - clrse - viewport.width * 0.33,
                hr = (box.right + clrse) - viewport.width,
                h = Math.min(hl, hr);
            window.scrollBy({left: Math.max(h, 0), top: Math.max(v, 0), behavior: 'smooth'});
        }
    }
});

Vue.component('proof-trace-node', {
    props: ['value', 'status'],
    data: () => ({_anchor: false}),
    template: `
        <div class="proof-trace-node" :class="[value.tag, statusClass]"
                @click="toggle" @click.capture="clickCapture"
                @mouseenter="showId" @mouseleave="hideId" @mousedown="clickStart"
                @mouseover="showRefs" @mouseout="hideRefs">
            <div @mousedown="stopDbl" class="title">
                <span class="pp">{{value.pp}}</span>
                <span class="tag">{{tag}}</span>
            </div>
            <proof-trace-goal v-if="value.goal" :value="value.goal"
                @click.native.stop="action"/>
        </div>`,
    computed: {
        tag() {
            return (this.value.tag == Data.NodeType.AndNode) ? this.value.id[0]
                    : this.value.id.slice(0, 2)
                        .reverse().filter((n:number) => n >= 0).join('→');
        },
        statusClass() {
            return this.status && `${this.status.tag}${this.status.from || ''}`;
        }
    },
    methods: {
        action(ev) { this.$emit('action', ev); },
        toggle() { this.action({type: 'expand/collapse', target: this.value}); },
        showId() { $('#hint').text(JSON.stringify(this.value.id)); },
        hideId() { $('#hint').empty(); },

        showRefs(ev) {
            var el = ev.target;
            if (['var', 'name'].some(c => el.classList.contains(c))) {
                this.varSpans(el.textContent).addClass('highlight');
            }
        },
        hideRefs() {
            this.varSpans().removeClass('highlight');
        },
        varSpans(nm?: string) {
            if (nm) return this.varSpans().filter((_,x: Node) => x.textContent == nm);
            else {
                var el = $(this.$el);
                return el.find('span.var').add(el.find('.proof-trace-vars span.name'));
            }
        },

        stopDbl(ev) { if (ev.detail > 1) ev.preventDefault(); },
        // boilerplate to prevent click after selection
        clickStart(ev) { this.$data._anchor = {x: ev.pageX, y: ev.pageY}; },
        clickCapture(ev) { 
            var a = this.$data._anchor;
            if (a && (Math.abs(ev.pageX - a.x) > 3 || Math.abs(ev.pageY - a.y) > 3))
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
        <div class="proof-trace-vars" v-show="value.length > 0">
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
