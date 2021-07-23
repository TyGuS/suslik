<template>
    <div id="proof-trace-pane" class="ide-pane proof-trace-pane"
            :class="{'proof-trace-filter--only-success': options.proofOnly,
                     'proof-trace-filter--only-expanded': options.expandedOnly}"
            @mousedown="panStart" @mousemove="panMove" @mouseup="panEnd"
            @mousewheel="zoomPad" @scroll="onScroll">
        <app-toolbar :options="options" @action="toplevelAction($event)"/>
        <app-context-menu ref="contextMenu" @action="toplevelAction"/>
        <div ref="area">
            <template v-for="(doc,id) in docs">
                <div class="proof-trace-area" :key="id"
                        :class="{active: id === activeTrace}">
                    <div class="proof-trace-pane-rendered"
                            :style="{'--zoom': zoom/100}">
                        <proof-trace :root="doc.trace.root" :highlight="jointHigh"
                            @action="toplevelAction($event, id)"/>
                    </div>
                    <proof-interaction :choices="doc.interaction && doc.interaction.choices"
                        :result="doc.interaction && doc.interaction.result"
                        @action="$emit('interaction:action', {id, ...$event})"/>
                </div>
            </template>
        </div>
    </div>
</template>

<style>
.proof-trace-pane .proof-trace-area:not(.active) {
    display: none;
}
</style>

<script>
import AppToolbar from './app-toolbar.vue';
import AppContextMenu from './app-context-menu';
import ProofTrace from './proof-trace.vue';
import ProofInteraction from './proof-interaction.vue';


function bounded(val, min, max) { return Math.max(min, Math.min(max, val)); }


export default {
    data: () => ({docs: {}, options: {simple: false, auto: true}, zoom: 100, pscroll: {x: 0, y: 0},
                  activeTrace: undefined,
                  /* this is defunct for now... */
                  highlight: {'special': [[]]}}),
    computed: {
        jointHigh() {
            return {'interact-focus': this.interaction?.focused, ...this.highlight};
        }
    },
    mounted() {
        requestAnimationFrame(() =>
            this._areaOffset = {x: this.$refs.area.offsetLeft, y: this.$refs.area.offsetTop});
    },
    methods: {
        toplevelAction(ev, id) {
            ev = {id, ...ev};
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        },
        onScroll() {
            var sc = {x: this.$el.scrollLeft, y: this.$el.scrollTop};
            if (sc.x !== Math.round(this.pscroll.x) || sc.y !== Math.round(this.pscroll.y))
                this.pscroll = sc;
        },
        setZoom(newValue, around = {x:0, y:0}) {
            var u = this.zoom, v = this.zoom = newValue,
                sc = {x: (this.pscroll.x - around.x) * v / u + around.x,
                      y: (this.pscroll.y - around.y) * v / u + around.y};
            this.$el.scrollTop = Math.round(sc.y);
            this.$el.scrollLeft = Math.round(sc.x);
            this.pscroll = sc;
        },
        panStart(ev) {
            if (!ev.target.closest('.proof-trace-node')) {
                this._gesture = {x: ev.x, y: ev.y}
            }
        },
        panMove(ev) {
            if (this._gesture) {
                var u = this._gesture, v = this._gesture = {x: ev.x, y: ev.y};
                this.$el.scrollTop -= v.y - u.y;
                this.$el.scrollLeft -= v.x - u.x;
            }
        },
        panEnd(ev) {
            this._gesture = undefined;
        },
        zoomPad(ev) {
            if (ev.ctrlKey) {
                var o = this._areaOffset,
                    xy = {x: o.x - (ev.pageX - this.$el.offsetLeft),
                          y: o.y - (ev.pageY - this.$el.offsetTop)};
                this.setZoom(bounded(this.zoom - ev.deltaY, 10, 100), xy);
                ev.stopPropagation();
                ev.preventDefault();
            }
        }
    },
    components: { AppToolbar, AppContextMenu, ProofTrace, ProofInteraction }
}
</script>
