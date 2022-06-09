<template>
    <vue-context ref="m">
        <li><a name="expandAll" @click="action">Expand all</a></li>
        <li><a name="copyNodeId" @click="action">Copy Node Id</a></li>
        <li><a name="copyGoal" @click="action">Copy goal</a></li>
    </vue-context>  
</template>

<script>
import VueContext from 'vue-context';


export default {
    components: {VueContext},
    methods: {
        open(ev /*: View.ActionEvent*/) {
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
}
</script>
