<template>
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
    </div>
</template>

<script>
import $ from 'jquery';
import { ProofTrace } from '../ts/proof-trace';
import ProofTraceGoal from './proof-trace-goal.vue';


export default {
    props: ['value', 'status', 'derivation', 'numDescendants'],
    data: () => ({_anchor: false}),
    computed: {
        tag() {
            var pfx = (this.value.tag == ProofTrace.Data.NodeType.OrNode) ? 2 : 1;
            return this.value.id.slice(0, pfx)
                   .reverse().filter(n => n >= 0).join('→');
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
        showId() {
            // temporary: show derivation trail in hint
            var d = this.derivation;
            if (d) {
                var subst = Object.entries(d.subst).map(([k,v]) => `${k} ↦ ${v}`);
                $('#hint').text(`${d.ruleName} @ ${subst.join(', ')}`);
            }
            else
                $('#hint').text(JSON.stringify(this.value.id));
        },
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
        varSpans(nm) {
            if (nm) return this.varSpans().filter((_, x) => x.textContent == nm);
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
    },
    components: { ProofTraceGoal }
}
</script>
