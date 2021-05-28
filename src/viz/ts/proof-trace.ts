import arreq from 'array-equal';
import $ from 'jquery';
import Vue from 'vue';
import { VueContext } from 'vue-context'
import 'vue-context/dist/css/vue-context.css';

import './proof-trace.css';
import './menu.css';



class ProofTrace {

    data: Data
    root: Data.NodeEntry

    nodeIndex: {
        byId: JSONMap<Data.NodeId, Data.NodeEntry>
        childrenById: JSONMap<Data.NodeId, Data.NodeEntry[]>
        subtreeSizeById: JSONMap<Data.NodeId, number>
        statusById: JSONMap<Data.NodeId, Data.StatusEntry>
        viewById: JSONMap<Data.NodeId, View.Node>
    }

    view: Vue & {root: View.Node}

    constructor(data: ProofTrace.Data) {
        this.data = data;
        this.root = this.data.nodes[0];

        this.createIndex();
        this.createView();
    }

    createIndex() {
        this.nodeIndex = {
            byId: new JSONMap(),
            childrenById: new JSONMap(), subtreeSizeById: new JSONMap(),
            statusById: new JSONMap(),
            viewById: new JSONMap()
        };
        // Build byId
        for (let node of this.data.nodes) {
            if (!this.nodeIndex.byId.get(node.id))
                this.nodeIndex.byId.set(node.id, node);
        }

        // Build childrenById
        for (let node of this.data.nodes) {
            if (node.id.length >= 1) {
                var parent = node.id.slice(1);
                this.addChild(parent, node);
            }
        }

        // Build statusById
        for (let entry of this.data.statuses) {
            var id = entry.at;
            this.nodeIndex.statusById.set(id, entry);
        }

        for (let node of this.data.nodes.sort((a, b) => b.id.length - a.id.length)) {
            if (!this.nodeIndex.statusById.get(node.id)) {
                let children = (this.nodeIndex.childrenById.get(node.id) || [])
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

        // Build subtreeSizeById
        var sz = this.nodeIndex.subtreeSizeById;
        for (let node of this.data.nodes.sort((a, b) => b.id.length - a.id.length)) {
            let children = (this.nodeIndex.childrenById.get(node.id) || []);
            sz.set(node.id, 1 + children.map(u => sz.get(u.id) || 1)
                                        .reduce((x,y) => x + y, 0));
        }
    }

    addChild(parent: Data.NodeId, child: Data.NodeEntry) {
        var m = this.nodeIndex.childrenById;
        // Note: nodes can re-occur if they were suspended during the search
        var l = m.get(parent) || [];
        if (!l.some(u => arreq(u.id, child.id)))
            m.set(parent, l.concat([child]));
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
        this.view = new (Vue.component('proof-trace-pane'))();
        this.view.root = this.createNode(this.root);
        this.expandNode(this.view.root);
        this.expandNode(this.view.root.children[0]);
        this.view.$mount();

        this.view.$on('action', (ev: View.ActionEvent) => this.viewAction(ev));
    }

    getStatus(node: Data.NodeEntry): Data.GoalStatusEntry { 
        var entry = this.nodeIndex.statusById.get(node.id);
        return entry && entry.status;
    }

    getSubtreeSize(node: Data.NodeEntry): number { 
        return this.nodeIndex.subtreeSizeById.get(node.id) || 1;
    }

    createNode(node: Data.NodeEntry): View.Node {
        var v = {value: node, children: undefined, focus: false, expanded: false,
                 status: this.getStatus(node),
                 numDescendants: this.getSubtreeSize(node)};
        this.nodeIndex.viewById.set(node.id, v);
        return v;
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

    expandById(node: Data.NodeId, focus: boolean = false) {
        var view = this.nodeIndex.viewById.get(node);
        if (view) this.expandNode(view, focus);
    }

    expandByIds(nodes: Data.NodeId[]) {
        var sorted = nodes.slice().sort((a, b) => a.length - b.length);
        for (let node of sorted) this.expandById(node);
    }

    expandBranch(tip: Data.NodeId, focus: boolean = false) {
        var prefixes = tip.slice(1).map((_,i,u) => u.slice(-(i + 1)));
        for (let pfx of prefixes)
            this.expandById(pfx);
        // @todo focus tip
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
        case 'copyNodeId':
            this.copyJson(ev.target.value.id); break;
        }
    }

    copyJson(o: any) { 
        navigator.clipboard.writeText(JSON.stringify(o));
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
            id: string
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

        export type GoalStatusEntry = {tag: "Succeeded" | "Failed", from?: string | string[]};

        export function parse(traceText: string): Data {
            var entries = traceText.split('\n\n').filter(x => x).map(ln =>
                            JSON.parse(ln));
            var nodes = [], statuses = [];
            for (let e of entries) {
                if (["AndNode", "OrNode"].includes(e.tag)) nodes.push(e);
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
            numDescendants: number
            status: Data.GoalStatusEntry
            focus: boolean
            expanded: boolean
        };

        export type ActionEvent = {
            type: "expand" | "collapse" | "expandAll" | "menu"
                | "copyNodeId" | "copyGoalId" | "copyGoal",
            target: Node
            $event: MouseEvent
        };

        const OPERATORS = new Map([
            [':->', {pp: "↦"}], ['==', {pp: "="}], ['**', {pp: '∗'}], ['&&', {pp: "∧"}],
            ['not', {pp: "¬"}], ['=i', {pp: "=ᵢ"}], ['++', {pp: '∪'}]]);

        export function tokenize(pp: string, env: Data.Environment) {
            return pp.split(/(\s+|[(){}[\],])/).map(s => {
                var v = env.get(s), op = OPERATORS.get(s), mo: RegExpMatchArray;
                if (v)
                    return {kind: 'var', text: s, pp: pprintIdentifier(s), ...v};
                else if (op)
                    return {kind: 'op', text: s, ...op};
                else if (s.match(/^\s+$/))
                    return {kind: 'whitespace', text: s};
                else if (s.match(/^[(){}[\]]$/))
                    return {kind: 'brace', text: s};
                else if (mo = s.match(/^<(\w+)>$/)) {
                    return {kind: 'cardinality', text: s, pp: pprintIdentifier(mo[1])};
                }
                else if (s != '')
                    return {kind: 'unknown', text: s};
            })
            .filter(x => x);
        }

        export function pprintIdentifier(v: string) {
            return v.replace('_alpha_', 'α');
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


Vue.component('proof-trace-pane', {
    props: ['root'],
    data: () => ({options: {}, zoom: 1}),
    template: `
        <div id="proof-trace-pane" 
            :class="{'proof-trace-filter--only-success': options.proofOnly,
                     'proof-trace-filter--only-expanded': options.expandedOnly}">
            <proof-trace-toolbar :options="options"/>
            <proof-trace-context-menu ref="contextMenu" @action="toplevelAction"/>
            <div class="proof-trace-pane-area" :style="{'--zoom': zoom}">
                <proof-trace :root="root" @action="toplevelAction"/>
            </div>
        </div>`,
    methods: {
        toplevelAction(ev) {
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        }
    }
});

Vue.component('proof-trace', {
    props: ['root'],
    data: () => ({statusClass: undefined}),
    template: `
        <div class="proof-trace" :class="[statusClass, root && root.children && root.children.length == 0 ? 'no-children' : 'has-children']">
            <template v-if="root">
                <proof-trace-node ref="nroot" :value="root.value"
                                  :status="root.status" :num-descendants="root.numDescendants"
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
        if (this.$refs.nroot)
            this.statusClass = this.$refs.nroot.statusClass;
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
    props: ['value', 'status', 'numDescendants'],
    data: () => ({_anchor: false}),
    template: `
        <div class="proof-trace-node" :class="[value.tag, statusClass]"
                @click="toggle" @click.capture="clickCapture"
                @mouseenter="showId" @mouseleave="hideId" @mousedown="clickStart"
                @mouseover="showRefs" @mouseout="hideRefs"
                @contextmenu.prevent="action({type: 'menu', $event})">
            <div @mousedown="stopDbl" class="title">
                <span class="pp">{{value.pp}}</span>
                <span class="cost" v-if="value.cost >= 0">{{value.cost}}</span>
                <span class="num-descendants">{{numDescendants}}</span>
                <span class="goal-id" v-if="value.goal">{{value.goal.id}}</span>
                <span class="tag" v-else>{{tag}}</span>
            </div>
            <proof-trace-goal v-if="value.goal" :value="value.goal"
                @click.native.stop="action"/>
        </div>`,
    computed: {
        tag() {
            var pfx = (this.value.tag == Data.NodeType.OrNode) ? 2 : 1;
            return this.value.id.slice(0, pfx)
                   .reverse().filter((n:number) => n >= 0).join('→');
        },
        statusClass() {
            if (this.status) {
                var {tag, from: fr} = this.status,
                    suffix = fr ? (fr === '*' ? '*' : `-${fr}`) : ''
                return `${tag}${suffix}`;
            }
            else return undefined;
        }
    },
    methods: {
        action(ev) { this.$emit('action', ev); },
        toggle() { this.action({type: 'expand/collapse', target: this.value}); },
        showId() { $('#hint').text(JSON.stringify(this.value.id)); },
        hideId() { $('#hint').empty(); },

        showRefs(ev) {
            var el = ev.target;
            if (['var', 'name', 'cardinality'].some(c => el.classList.contains(c))) {
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
                return el.find('span.var, span.cardinality, .proof-trace-vars span.name');
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
                    <span class="name">{{pp(v[1])}}</span>
                </span>
            </template>
        </div>`,
    methods: {
        pp: View.pprintIdentifier
    }
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
});

Vue.component('proof-trace-toolbar', {
    props: {options: {default: () => ({})}},
    template: `
        <div class="proof-trace-toolbar">
            <form>
                Show:
                <input type="checkbox" name="proof-only" id="proof-only" v-model="options.proofOnly">
                <label for="proof-only">Proof only</label>
                <input type="checkbox" name="expanded-only" id="expanded-only" v-model="options.expandedOnly">
                <label for="expended-only">Expanded only</label>
            </form>
        </div>`
});

Vue.component('proof-trace-context-menu', {
    template: `
        <vue-context ref="m">
            <li><a name="expandAll" @click="action">Expand all</a></li>
            <li><a name="copyNodeId" @click="action">Copy Node Id</a></li>
            <li><a name="copyGoal" @click="action">Copy goal</a></li>
        </vue-context>`,
    components: {VueContext},
    methods: {
        open(ev: View.ActionEvent) {
            this._target = ev.target;
            this.$refs.m.open(ev.$event);
        },
        action(ev) {
            this.$emit('action', {
                type: ev.currentTarget.name,
                target: this._target
            });
        }
    }
});



export { ProofTrace }
