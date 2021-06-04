<template>
    <div id="proof-trace-pane" 
        :class="{'proof-trace-filter--only-success': options.proofOnly,
                    'proof-trace-filter--only-expanded': options.expandedOnly}">
        <app-toolbar :options="options"/>
        <app-context-menu ref="contextMenu" @action="toplevelAction"/>
        <div class="proof-trace-pane-area" :style="{'--zoom': zoom}">
            <proof-trace :root="root" @action="toplevelAction"/>
        </div>
    </div>
</template>

<script>
import AppToolbar from './app-toolbar.vue';
import AppContextMenu from './app-context-menu';
import ProofTrace from './proof-trace.vue';


export default {
    props: ['root'],
    data: () => ({options: {}, zoom: 1}),
    methods: {
        toplevelAction(ev) {
            switch (ev.type) {
            case 'menu': this.$refs.contextMenu.open(ev); break;
            }
            this.$emit('action', ev);
        }
    },
    components: { AppToolbar, AppContextMenu, ProofTrace }
}
</script>
